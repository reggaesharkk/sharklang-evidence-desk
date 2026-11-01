# Changelog

## 0.1.1 — 1 November 2026

- The app bundle now launches directly with `python SHARKLANG_EVIDENCE_DESK_0.1.1_20261101.zip`; it does not need to be extracted first.
- The browser UI and its assets load from inside the app ZIP.
- The release ZIP being checked is still read in place and is not extracted or executed.
- Added JSON report download; the report can contain archive paths, so review it before sharing.

## 0.1.0 — 1 November 2026

- First local ZIP structure, SHA-256 manifest, and credential-pattern review prototype.
- Optional Gemini explanation is gated through the bundled SharkLang runtime and local Witness.
