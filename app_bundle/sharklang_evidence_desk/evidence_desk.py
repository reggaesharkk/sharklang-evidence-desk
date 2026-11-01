#!/usr/bin/env python3
"""Local, read-only release ZIP auditor with optional SharkLang-gated Gemini explanation."""

from __future__ import annotations

import argparse
import hashlib
import getpass
import importlib.resources
import io
import json
import os
from pathlib import PurePosixPath
import posixpath
import re
import stat
import sys
import tempfile
import urllib.error
import webbrowser
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import Any
from urllib.parse import unquote, urlsplit
from zipfile import BadZipFile, ZipFile

if __package__:
    from .sharklang import BytecodeCompiler, SharkEgressClient, SharkPKI, SharkVM, SharkWitnessServer
else:
    from sharklang import BytecodeCompiler, SharkEgressClient, SharkPKI, SharkVM, SharkWitnessServer


APP_VERSION = "0.1.1"
GEMINI_MODEL = "gemini-3.5-flash-lite"
MAX_UPLOAD_BYTES = 50 * 1024 * 1024
MAX_ENTRY_COUNT = 4000
MAX_TOTAL_UNCOMPRESSED_BYTES = 100 * 1024 * 1024
MAX_TEXT_SCAN_BYTES = 1024 * 1024
MAX_MANIFEST_BYTES = 2 * 1024 * 1024
READ_CHUNK_BYTES = 64 * 1024

TEXT_SUFFIXES = {
    ".c", ".cfg", ".conf", ".csv", ".css", ".html", ".ini", ".json", ".js",
    ".lean", ".log", ".md", ".py", ".rst", ".sh", ".sum", ".toml", ".txt",
    ".yaml", ".yml", ".xml", ".sha256", ".sha256sum",
}
MANIFEST_SUFFIXES = {".txt", ".sum", ".sha256", ".sha256sum", ".sha256sums"}
MANIFEST_LINE = re.compile(r"^\s*([0-9a-fA-F]{64})\s+\*?(.+?)\s*$")
SECRET_PATTERNS: tuple[tuple[str, re.Pattern[bytes]], ...] = (
    ("private_key_block", re.compile(rb"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----")),
    ("google_api_key_like", re.compile(rb"\bAIza[0-9A-Za-z_-]{25,}\b")),
    ("github_token_like", re.compile(rb"\bgh[pousr]_[A-Za-z0-9_]{30,}\b")),
    ("openrouter_key_like", re.compile(rb"\bsk-or-v1-[A-Za-z0-9_-]{30,}\b")),
    ("groq_key_like", re.compile(rb"\bgsk_[A-Za-z0-9_-]{30,}\b")),
    ("together_key_like", re.compile(rb"\btgp_v1_[A-Za-z0-9_-]{30,}\b")),
    ("aws_access_key_like", re.compile(rb"\bAKIA[0-9A-Z]{16}\b")),
)
SENSITIVE_FILENAMES = {".env", ".npmrc", "id_rsa", "id_ed25519", "credentials.json"}
SENSITIVE_SUFFIXES = {".key", ".pem", ".p12", ".pfx"}


class AuditInputError(ValueError):
    """A ZIP that is too large or cannot be safely inspected."""


def _safe_archive_name(raw_name: str) -> tuple[str | None, str | None]:
    if "\x00" in raw_name:
        return None, "NUL byte in archive path"
    normalized_slashes = raw_name.replace("\\", "/")
    if normalized_slashes.startswith("/") or re.match(r"^[A-Za-z]:", normalized_slashes):
        return None, "absolute or drive-qualified archive path"
    parts = PurePosixPath(normalized_slashes).parts
    if ".." in parts:
        return None, "parent-directory traversal in archive path"
    normalized = posixpath.normpath(normalized_slashes)
    if normalized in {"", "."}:
        return None, "empty archive path"
    return normalized, None


def _looks_like_manifest(path: str) -> bool:
    name = PurePosixPath(path).name.lower()
    suffix = PurePosixPath(name).suffix
    return suffix in MANIFEST_SUFFIXES and any(
        marker in name for marker in ("sha256", "checksum", "manifest")
    )


def _manifest_path(base: str, listed: str) -> tuple[str | None, str | None]:
    candidate = listed.strip().replace("\\", "/")
    if not candidate or candidate.startswith("/") or re.match(r"^[A-Za-z]:", candidate):
        return None, "absolute or empty path in manifest"
    if ".." in PurePosixPath(candidate).parts:
        return None, "parent-directory traversal in manifest"
    joined = posixpath.normpath(posixpath.join(base, candidate))
    if joined == ".." or joined.startswith("../"):
        return None, "manifest path escapes its archive directory"
    return joined, None


def _manifest_checks(
    archive: ZipFile,
    normalized_to_raw: dict[str, str],
    file_hashes: dict[str, str],
    file_paths: list[str],
) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    manifest_paths = sorted(path for path in normalized_to_raw if _looks_like_manifest(path))
    for manifest_path in manifest_paths:
        entry: dict[str, Any] = {
            "manifest": manifest_path,
            "status": "OPEN",
            "listed": 0,
            "matched": 0,
            "missing": [],
            "mismatched": [],
            "unlisted": [],
            "problems": [],
        }
        try:
            info = archive.getinfo(normalized_to_raw[manifest_path])
            if info.file_size > MAX_MANIFEST_BYTES:
                entry["problems"].append("manifest exceeds the 2 MiB reading limit")
                results.append(entry)
                continue
            raw = archive.read(info)
            text = raw.decode("utf-8-sig")
        except (KeyError, OSError, BadZipFile, UnicodeError, RuntimeError):
            entry["problems"].append("manifest could not be read as UTF-8 text")
            results.append(entry)
            continue

        base = posixpath.dirname(manifest_path)
        expected: set[str] = set()
        for line_number, line in enumerate(text.splitlines(), start=1):
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            match = MANIFEST_LINE.fullmatch(line)
            if not match:
                entry["problems"].append(f"line {line_number} is not a SHA-256 entry")
                continue
            digest, listed = match.groups()
            normalized, problem = _manifest_path(base, listed)
            if problem or normalized is None:
                entry["problems"].append(f"line {line_number}: {problem or 'invalid path'}")
                continue
            if normalized == manifest_path:
                entry["problems"].append(f"line {line_number} tries to hash the manifest itself")
                continue
            if normalized in expected:
                entry["problems"].append(f"line {line_number} repeats {normalized}")
                continue
            expected.add(normalized)
            entry["listed"] += 1
            actual_hash = file_hashes.get(normalized)
            if actual_hash is None:
                entry["missing"].append(normalized)
            elif actual_hash.lower() != digest.lower():
                entry["mismatched"].append(normalized)
            else:
                entry["matched"] += 1

        actual_scope = {
            path
            for path in file_paths
            if path != manifest_path
            and (not base or path.startswith(base.rstrip("/") + "/"))
        }
        entry["unlisted"] = sorted(actual_scope - expected)[:100]
        if entry["missing"] or entry["mismatched"] or entry["problems"]:
            entry["status"] = "FAIL"
        elif entry["listed"] == 0 or entry["unlisted"]:
            entry["status"] = "OPEN"
        else:
            entry["status"] = "PASS"
        results.append(entry)
    return results


def audit_archive(data: bytes, display_name: str) -> dict[str, Any]:
    if not data:
        raise AuditInputError("The selected ZIP is empty.")
    if len(data) > MAX_UPLOAD_BYTES:
        raise AuditInputError("ZIP exceeds the 50 MiB upload limit.")
    try:
        archive = ZipFile(io.BytesIO(data), "r")
    except (BadZipFile, OSError):
        raise AuditInputError("This file is not a readable ZIP archive.") from None

    with archive:
        infos = archive.infolist()
        if len(infos) > MAX_ENTRY_COUNT:
            raise AuditInputError("ZIP contains more than 4,000 entries.")
        declared_uncompressed = sum(info.file_size for info in infos if not info.is_dir())
        if declared_uncompressed > MAX_TOTAL_UNCOMPRESSED_BYTES:
            raise AuditInputError("ZIP expands beyond the 100 MiB inspection limit.")

        unsafe_paths: list[dict[str, str]] = []
        collisions: list[str] = []
        symlinks: list[str] = []
        encrypted: list[str] = []
        normalized_to_raw: dict[str, str] = {}
        casefolded: dict[str, str] = {}
        file_infos: list[tuple[str, Any]] = []

        for info in infos:
            normalized, problem = _safe_archive_name(info.filename)
            if problem or normalized is None:
                unsafe_paths.append({"path": info.filename[:240], "reason": problem or "invalid path"})
                continue
            if normalized in normalized_to_raw:
                collisions.append(normalized)
            normalized_to_raw[normalized] = info.filename
            folded = normalized.casefold()
            other = casefolded.get(folded)
            if other is not None and other != normalized:
                collisions.append(f"{other} / {normalized} (case-insensitive collision)")
            casefolded[folded] = normalized
            if info.is_dir():
                continue
            file_infos.append((normalized, info))
            mode = info.external_attr >> 16
            if stat.S_ISLNK(mode):
                symlinks.append(normalized)
            if info.flag_bits & 0x1:
                encrypted.append(normalized)

        file_hashes: dict[str, str] = {}
        file_paths: list[str] = []
        secret_findings: list[dict[str, str]] = []
        unreadable_files: list[str] = []
        bytes_read_total = 0

        for path, info in file_infos:
            file_paths.append(path)
            if info.flag_bits & 0x1:
                unreadable_files.append(path)
                continue
            file_hash = hashlib.sha256()
            can_text_scan = PurePosixPath(path).suffix.lower() in TEXT_SUFFIXES
            scan_buffer = bytearray() if can_text_scan and info.file_size <= MAX_TEXT_SCAN_BYTES else None
            try:
                with archive.open(info, "r") as stream:
                    while True:
                        chunk = stream.read(READ_CHUNK_BYTES)
                        if not chunk:
                            break
                        bytes_read_total += len(chunk)
                        if bytes_read_total > MAX_TOTAL_UNCOMPRESSED_BYTES:
                            raise AuditInputError("ZIP exceeded the 100 MiB inspection limit while reading.")
                        file_hash.update(chunk)
                        if scan_buffer is not None:
                            scan_buffer.extend(chunk)
                file_hashes[path] = file_hash.hexdigest()
            except AuditInputError:
                raise
            except (BadZipFile, OSError, RuntimeError, NotImplementedError, EOFError):
                unreadable_files.append(path)
                continue

            lower_name = PurePosixPath(path).name.lower()
            suffix = PurePosixPath(path).suffix.lower()
            if lower_name in SENSITIVE_FILENAMES or suffix in SENSITIVE_SUFFIXES or lower_name.startswith(".env."):
                secret_findings.append({"path": path, "kind": "credential_like_filename"})
            if scan_buffer is not None:
                for label, pattern in SECRET_PATTERNS:
                    if pattern.search(scan_buffer):
                        secret_findings.append({"path": path, "kind": label})

        # Report one finding per path and rule, even if the same text occurs repeatedly.
        secret_findings = list({(item["path"], item["kind"]): item for item in secret_findings}.values())
        manifests = _manifest_checks(archive, normalized_to_raw, file_hashes, file_paths)

    manifest_fail = any(item["status"] == "FAIL" for item in manifests)
    manifest_open = not manifests or any(item["status"] == "OPEN" for item in manifests)
    structure_fail = bool(unsafe_paths or collisions or symlinks or encrypted or unreadable_files)
    integrity_status = "FAIL" if structure_fail or manifest_fail else (
        "OPEN" if manifest_open else "PASS"
    )
    overall_status = "FAIL" if structure_fail or manifest_fail else (
        "REVIEW" if secret_findings else "OPEN"
    )

    checks = [
        {
            "name": "ZIP structure and file checks",
            "status": "FAIL" if structure_fail else "PASS",
            "details": {
                "files": len(file_paths),
                "declared_uncompressed_bytes": declared_uncompressed,
                "unsafe_paths": unsafe_paths[:100],
                "name_collisions": sorted(set(collisions))[:100],
                "symbolic_links": symlinks[:100],
                "encrypted_files": encrypted[:100],
                "unreadable_or_corrupt_files": unreadable_files[:100],
            },
        },
        {
            "name": "SHA-256 manifests",
            "status": "FAIL" if manifest_fail else ("OPEN" if manifest_open else "PASS"),
            "details": manifests,
        },
        {
            "name": "Credential pattern scan",
            "status": "REVIEW" if secret_findings else "PASS",
            "details": {
                "heuristic_only": True,
                "scan_limit_bytes_per_text_file": MAX_TEXT_SCAN_BYTES,
                "findings": secret_findings[:100],
            },
        },
        {
            "name": "Test and proof replay",
            "status": "OPEN",
            "details": "The auditor does not execute code, run tests, or validate mathematical proofs.",
        },
    ]

    return {
        "app_version": APP_VERSION,
        "archive_name": PurePosixPath(display_name.replace("\\", "/")).name[:160],
        "overall_status": overall_status,
        "integrity_status": integrity_status,
        "file_count": len(file_paths),
        "declared_uncompressed_bytes": declared_uncompressed,
        "bytes_read": bytes_read_total,
        "manifest_count": len(manifests),
        "manifest_pass_count": sum(item["status"] == "PASS" for item in manifests),
        "manifest_fail_count": sum(item["status"] == "FAIL" for item in manifests),
        "manifest_open_count": sum(item["status"] == "OPEN" for item in manifests),
        "secret_finding_count": len(secret_findings),
        "unsafe_path_count": len(unsafe_paths),
        "structure_fail": structure_fail,
        "can_explain": not structure_fail and not secret_findings,
        "checks": checks,
        "notice": (
            "This is a local structural audit. A PASS on ZIP or hashes does not prove code is safe, "
            "tests passed, a theorem is correct, or a release claim is true."
        ),
    }


def _summary_for_provider(report: dict[str, Any]) -> dict[str, Any]:
    """Return aggregate status/counts only; never include filenames or archive contents."""
    return {
        "overall_status": report["overall_status"],
        "integrity_status": report["integrity_status"],
        "file_count": report["file_count"],
        "manifest_count": report["manifest_count"],
        "manifest_pass_count": report["manifest_pass_count"],
        "manifest_fail_count": report["manifest_fail_count"],
        "manifest_open_count": report["manifest_open_count"],
        "unsafe_path_count": report["unsafe_path_count"],
        "secret_finding_count": report["secret_finding_count"],
        "test_replay": "OPEN_NOT_RUN",
    }


def _explain_with_gemini(report: dict[str, Any]) -> dict[str, Any]:
    if not report.get("can_explain"):
        raise ValueError("Gemini explanation is disabled when the ZIP is unreadable or a credential pattern was found.")

    key_was_present = bool(os.environ.get("GEMINI_API_KEY", "").strip())
    api_key = os.environ.get("GEMINI_API_KEY", "").strip()
    if not api_key:
        api_key = getpass.getpass("Enter GEMINI_API_KEY (hidden; not saved): ").strip()
    if not api_key:
        raise ValueError("No key entered; no provider request was made.")

    policy_source = """
# User clicked Explain. Only an aggregate audit summary may leave this computer.
let user_consented: Bool = true;
let summary_only: Bool = true;
let no_credential_finding: Bool = true;
if (user_consented and summary_only and no_credential_finding) {
    emit egress_allowed = 1;
} else {
    emit egress_allowed = 0;
}
"""
    bytecode = BytecodeCompiler.compile(policy_source)
    execution = SharkVM(max_steps=100).run(bytecode)
    if execution.outputs.get("egress_allowed") != 1:
        raise ValueError("SharkLang policy blocked the explanation request.")
    bytecode_sha256 = hashlib.sha256(bytecode.to_canonical_bytes()).hexdigest()

    safe_summary = _summary_for_provider(report)
    prompt = (
        "Explain this local release ZIP audit in plain English, in at most three short bullets. "
        "Describe only what these checks establish. Make clear that tests and mathematical claims "
        "were not verified. Do not infer that the archive is secure or that its research claims are true.\n"
        "Aggregate audit summary (no filenames or file contents):\n"
        + json.dumps(safe_summary, sort_keys=True)
    )
    governor_state = {
        "app": "sharklang_evidence_desk",
        "user_clicked_explain": True,
        "data_class": "aggregate_counts_only",
        "archive_content_included": False,
        "credential_findings": 0,
        "summary_sha256": hashlib.sha256(
            json.dumps(safe_summary, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest(),
    }

    previous_key = os.environ.get("GEMINI_API_KEY")
    if not key_was_present:
        os.environ["GEMINI_API_KEY"] = api_key
    try:
        with tempfile.TemporaryDirectory(prefix="sharklang_evidence_desk_") as temp_dir:
            pki_dir = Path(temp_dir)
            SharkPKI.generate_all(pki_dir)
            witness = SharkWitnessServer(pki_dir, bind_port=0)
            port = witness.start_background()
            try:
                client = SharkEgressClient(pki_dir, port=port)
                result = client.execute_governed_api_call(
                    1,
                    "gemini",
                    prompt,
                    model=GEMINI_MODEL,
                    governor_state=governor_state,
                    bytecode_sha256=bytecode_sha256,
                    dry_run=False,
                )
            finally:
                witness.stop()
    finally:
        if previous_key is None:
            os.environ.pop("GEMINI_API_KEY", None)
        else:
            os.environ["GEMINI_API_KEY"] = previous_key
        api_key = ""

    response = result.get("response", {})
    choices = response.get("choices", []) if isinstance(response, dict) else []
    first = choices[0] if isinstance(choices, list) and choices else {}
    message = first.get("message", {}) if isinstance(first, dict) else {}
    answer = message.get("content", "") if isinstance(message, dict) else ""
    usage = response.get("usage", {}) if isinstance(response, dict) else {}
    return {
        "status": result.get("status"),
        "provider": "gemini",
        "model": response.get("model", GEMINI_MODEL) if isinstance(response, dict) else GEMINI_MODEL,
        "http_status": result.get("http_status"),
        "answer": str(answer)[:4000],
        "usage": {
            name: usage[name]
            for name in ("prompt_tokens", "completion_tokens", "total_tokens", "cost")
            if isinstance(usage, dict) and name in usage
        },
        "witness_status": result.get("witness_receipt", {}).get("status"),
    }


class EvidenceServer(HTTPServer):
    def __init__(self, address: tuple[str, int], handler: type[BaseHTTPRequestHandler]) -> None:
        super().__init__(address, handler)
        self.latest_report: dict[str, Any] | None = None


class EvidenceHandler(BaseHTTPRequestHandler):
    server: EvidenceServer

    def log_message(self, _format: str, *args: object) -> None:
        # Keep filenames, request details, and local use out of terminal logs.
        return

    def _headers_ok(self) -> bool:
        port = self.server.server_port
        allowed_hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
        if self.headers.get("Host", "") not in allowed_hosts:
            self.send_error(403)
            return False
        origin = self.headers.get("Origin")
        allowed_origins = {f"http://127.0.0.1:{port}", f"http://localhost:{port}"}
        if origin and origin not in allowed_origins:
            self.send_error(403)
            return False
        return True

    def _send_bytes(self, status: int, body: bytes, content_type: str) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header(
            "Content-Security-Policy",
            "default-src 'self'; style-src 'self'; script-src 'self'; connect-src 'self'; "
            "object-src 'none'; base-uri 'none'; frame-ancestors 'none'",
        )
        self.end_headers()
        self.wfile.write(body)

    def _send_json(self, status: int, value: dict[str, Any]) -> None:
        body = json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        self._send_bytes(status, body, "application/json; charset=utf-8")

    @staticmethod
    def _read_asset(name: str) -> bytes:
        if __package__:
            return importlib.resources.files(__package__).joinpath(name).read_bytes()
        return Path(__file__).with_name(name).read_bytes()

    def do_GET(self) -> None:
        if not self._headers_ok():
            return
        path = urlsplit(self.path).path
        assets = {
            "/": ("index.html", "text/html; charset=utf-8"),
            "/app.js": ("app.js", "text/javascript; charset=utf-8"),
            "/style.css": ("style.css", "text/css; charset=utf-8"),
        }
        item = assets.get(path)
        if item is None:
            self._send_json(404, {"error": "Not found."})
            return
        try:
            content = self._read_asset(item[0])
        except OSError:
            self._send_json(500, {"error": "The local app asset could not be read."})
            return
        self._send_bytes(200, content, item[1])

    def do_POST(self) -> None:
        if not self._headers_ok():
            return
        path = urlsplit(self.path).path
        if path == "/api/audit":
            self._post_audit()
        elif path == "/api/explain":
            self._post_explain()
        else:
            self._send_json(404, {"error": "Not found."})

    def _content_length(self, maximum: int) -> int | None:
        raw = self.headers.get("Content-Length", "")
        try:
            size = int(raw)
        except ValueError:
            self._send_json(411, {"error": "A valid Content-Length header is required."})
            return None
        if size < 0 or size > maximum:
            self._send_json(413, {"error": "Request exceeds the local app size limit."})
            return None
        return size

    def _post_audit(self) -> None:
        length = self._content_length(MAX_UPLOAD_BYTES)
        if length is None:
            return
        content_type = self.headers.get("Content-Type", "").split(";", 1)[0].strip().lower()
        if content_type != "application/zip":
            self._send_json(415, {"error": "Send a ZIP file to the local audit screen."})
            return
        data = self.rfile.read(length)
        if len(data) != length:
            self._send_json(400, {"error": "The local upload was incomplete."})
            return
        display_name = unquote(self.headers.get("X-File-Name", "release.zip"))
        try:
            report = audit_archive(data, display_name)
        except AuditInputError as exc:
            self.server.latest_report = None
            self._send_json(400, {"error": str(exc)})
            return
        except Exception:
            self.server.latest_report = None
            self._send_json(500, {"error": "The archive could not be audited. No files were extracted."})
            return
        self.server.latest_report = report
        self._send_json(200, report)

    def _post_explain(self) -> None:
        report = self.server.latest_report
        if report is None:
            self._send_json(409, {"error": "Run a local ZIP audit first."})
            return
        if not report.get("can_explain"):
            self._send_json(
                409,
                {"error": "Explanation is blocked: fix unreadable archive entries or inspect credential-like findings first."},
            )
            return
        try:
            result = _explain_with_gemini(report)
        except urllib.error.HTTPError as exc:
            status_code = int(exc.code)
            request_id = (exc.headers.get("x-request-id", "") if exc.headers else "")[:100]
            error = f"Gemini returned HTTP {status_code}. Check that the key and model are enabled for this account."
            self._send_json(502, {"error": error, "request_id": request_id})
            return
        except urllib.error.URLError:
            self._send_json(502, {"error": "Could not connect to Gemini. The local ZIP audit remains available."})
            return
        except TimeoutError:
            self._send_json(504, {"error": "Gemini took too long to respond. The local ZIP audit remains available."})
            return
        except ValueError as exc:
            self._send_json(400, {"error": str(exc)})
            return
        except Exception:
            self._send_json(502, {"error": "The explanation request failed. No ZIP contents or filenames were sent."})
            return
        self._send_json(200, result)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Open the local SharkLang Evidence Desk.")
    parser.add_argument("--host", default="127.0.0.1", help="Loopback only by default.")
    parser.add_argument("--port", type=int, default=8765)
    args = parser.parse_args(argv)
    if args.host not in {"127.0.0.1", "localhost"}:
        parser.error("Evidence Desk only binds to this computer (127.0.0.1 or localhost).")
    if not 1 <= args.port <= 65535:
        parser.error("port must be between 1 and 65535")

    try:
        server = EvidenceServer((args.host, args.port), EvidenceHandler)
    except OSError:
        print(f"Port {args.port} is unavailable. Try: python .\\evidence_desk.py --port 8766", file=sys.stderr)
        return 2
    url = f"http://127.0.0.1:{server.server_port}/"
    print(f"SharkLang Evidence Desk {APP_VERSION} is running locally at {url}")
    print("ZIP checks stay on this computer. Press Ctrl+C here to stop the app.")
    webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nEvidence Desk stopped.")
    finally:
        server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
