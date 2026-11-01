const fileInput = document.querySelector("#zip-file");
const dropZone = document.querySelector("#drop-zone");
const selectedName = document.querySelector("#selected-name");
const auditButton = document.querySelector("#audit-button");
const explainButton = document.querySelector("#explain-button");
const saveReportButton = document.querySelector("#save-report-button");
const activity = document.querySelector("#activity");
const results = document.querySelector("#results");
const explanation = document.querySelector("#explanation");
let selectedFile = null;
let latestReport = null;

function setSelected(file) {
  if (!file) return;
  if (!file.name.toLowerCase().endsWith(".zip")) {
    activity.textContent = "Choose a .zip archive.";
    return;
  }
  if (file.size > 50 * 1024 * 1024) {
    activity.textContent = "This file is over the 50 MiB limit.";
    return;
  }
  selectedFile = file;
  latestReport = null;
  results.classList.add("hidden");
  explainButton.disabled = true;
  selectedName.textContent = `${file.name} · ${(file.size / 1024 / 1024).toFixed(2)} MiB`;
  auditButton.disabled = false;
  activity.textContent = "Ready for local checks.";
  explanation.classList.add("hidden");
}

fileInput.addEventListener("change", () => setSelected(fileInput.files?.[0]));
for (const eventName of ["dragenter", "dragover"]) {
  dropZone.addEventListener(eventName, (event) => {
    event.preventDefault();
    dropZone.classList.add("dragover");
  });
}
for (const eventName of ["dragleave", "drop"]) {
  dropZone.addEventListener(eventName, (event) => {
    event.preventDefault();
    dropZone.classList.remove("dragover");
  });
}
dropZone.addEventListener("drop", (event) => setSelected(event.dataTransfer?.files?.[0]));

function addText(parent, tagName, className, text) {
  const node = document.createElement(tagName);
  if (className) node.className = className;
  node.textContent = text;
  parent.append(node);
  return node;
}

function statusClass(status) {
  return String(status || "OPEN").toLowerCase();
}

function showReport(report) {
  latestReport = report;
  results.classList.remove("hidden");
  document.querySelector("#result-name").textContent = report.archive_name || "Release archive";
  const badge = document.querySelector("#overall-badge");
  badge.textContent = report.overall_status;
  badge.className = `badge ${statusClass(report.overall_status)}`;
  document.querySelector("#metric-files").textContent = report.file_count;
  document.querySelector("#metric-manifests").textContent = `${report.manifest_pass_count}/${report.manifest_count}`;
  document.querySelector("#metric-secrets").textContent = report.secret_finding_count;
  document.querySelector("#metric-integrity").textContent = report.integrity_status;

  const checks = document.querySelector("#checks");
  checks.replaceChildren();
  for (const check of report.checks || []) {
    const article = document.createElement("article");
    article.className = "check";
    const top = document.createElement("div");
    top.className = "check-top";
    addText(top, "span", "check-name", check.name);
    addText(top, "span", `check-status ${statusClass(check.status)}`, check.status);
    article.append(top);
    let summary = "";
    if (check.name.startsWith("ZIP structure")) {
      const detail = check.details || {};
      summary = `${detail.files ?? 0} files; ${detail.declared_uncompressed_bytes ?? 0} declared uncompressed bytes.`;
    } else if (check.name.startsWith("SHA-256")) {
      summary = (check.details || []).map((item) => `${item.manifest}: ${item.matched}/${item.listed} listed files match; ${item.missing.length} missing, ${item.mismatched.length} mismatched, ${item.unlisted.length} unlisted.`).join(" ") || "No SHA-256 manifest was found.";
    } else if (check.name.startsWith("Credential")) {
      const detail = check.details || {};
      summary = detail.findings?.length ? `${detail.findings.length} possible credential indicator(s). This pattern scan can produce false positives and cannot prove that no secrets are present.` : "No known pattern matched in the scanned text. This heuristic scan cannot prove that no secrets are present.";
    } else {
      summary = check.details;
    }
    addText(article, "p", "check-summary", summary);

    const details = [];
    if (check.name.startsWith("ZIP structure")) {
      for (const key of ["unsafe_paths", "name_collisions", "symbolic_links", "encrypted_files", "unreadable_or_corrupt_files"]) {
        for (const value of check.details?.[key] || []) {
          details.push(typeof value === "string" ? value : `${value.path}: ${value.reason}`);
        }
      }
    } else if (check.name.startsWith("SHA-256")) {
      for (const manifest of check.details || []) {
        for (const key of ["missing", "mismatched", "unlisted", "problems"]) {
          for (const value of manifest[key] || []) details.push(`${manifest.manifest}: ${value}`);
        }
      }
    } else if (check.name.startsWith("Credential")) {
      for (const item of check.details?.findings || []) details.push(`${item.kind}: ${item.path}`);
    }
    if (details.length) {
      const list = document.createElement("ul");
      list.className = "detail-list";
      for (const item of details.slice(0, 24)) addText(list, "li", "", item);
      if (details.length > 24) addText(list, "li", "", `…and ${details.length - 24} more`);
      article.append(list);
    }
    checks.append(article);
  }
  explainButton.disabled = !report.can_explain;
  explainButton.title = report.can_explain ? "Sends aggregate status/counts only." : "Fix ZIP read errors and inspect credential-like findings first.";
}

saveReportButton.addEventListener("click", () => {
  if (!latestReport) return;
  const blob = new Blob([JSON.stringify(latestReport, null, 2)], { type: "application/json" });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  const base = String(latestReport.archive_name || "release").replace(/[^A-Za-z0-9._-]+/g, "_");
  link.href = url;
  link.download = `${base}.audit.json`;
  document.body.append(link);
  link.click();
  link.remove();
  URL.revokeObjectURL(url);
});

auditButton.addEventListener("click", async () => {
  if (!selectedFile) return;
  auditButton.disabled = true;
  explainButton.disabled = true;
  activity.textContent = "Checking the ZIP locally…";
  explanation.classList.add("hidden");
  try {
    const response = await fetch("/api/audit", {
      method: "POST",
      headers: {
        "Content-Type": "application/zip",
        "X-File-Name": encodeURIComponent(selectedFile.name),
      },
      body: selectedFile,
    });
    const data = await response.json();
    if (!response.ok) throw new Error(data.error || "The local audit failed.");
    showReport(data);
    activity.textContent = "Local audit complete. The ZIP was not sent to Gemini.";
  } catch (error) {
    activity.textContent = error.message || "Could not complete the local audit.";
  } finally {
    auditButton.disabled = !selectedFile;
  }
});

explainButton.addEventListener("click", async () => {
  explainButton.disabled = true;
  explainButton.textContent = "Check the terminal…";
  activity.textContent = "The hidden Gemini key prompt is in the PowerShell window running this app.";
  try {
    const response = await fetch("/api/explain", { method: "POST" });
    const data = await response.json();
    if (!response.ok) throw new Error(data.error || "Gemini explanation failed.");
    explanation.replaceChildren();
    addText(explanation, "h4", "", `${data.provider} · ${data.model} · HTTP ${data.http_status}`);
    addText(explanation, "div", "answer", data.answer || "The provider returned an empty answer.");
    const usage = data.usage || {};
    const usageText = Object.keys(usage).length ? `Usage: ${JSON.stringify(usage)} · Witness: ${data.witness_status || "unknown"}` : `Witness: ${data.witness_status || "unknown"}`;
    addText(explanation, "small", "", usageText);
    explanation.classList.remove("hidden");
    activity.textContent = "Gemini explained the aggregate report. The archive and filenames were not sent.";
  } catch (error) {
    activity.textContent = error.message || "The explanation request failed. The local report is unchanged.";
  } finally {
    explainButton.textContent = "Explain with Gemini";
    explainButton.disabled = !selectedFile;
  }
});
