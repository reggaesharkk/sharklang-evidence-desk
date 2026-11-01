# SharkLang Evidence Desk 0.1.1

**Release date:** 1 November 2026  
**Author:** Prince Upadhyay · [GitHub](https://github.com/reggaesharkk) · [ORCID 0009-0002-1170-4487](https://orcid.org/0009-0002-1170-4487)

I built this local evaluation prototype to inspect a software or research release ZIP before review. It checks archive readability and paths, SHA-256 manifests, and selected credential patterns. It reads the archive in place; it does not extract or execute its contents.

## Download and run

Download the [app ZIP](https://raw.githubusercontent.com/reggaesharkk/sharklang-evidence-desk/main/dist/SHARKLANG_EVIDENCE_DESK_0.1.1_20261101.zip). On Windows, with Python 3.10 or newer, open PowerShell in Downloads and run:

```powershell
Set-Location "$env:USERPROFILE\Downloads"
python .\SHARKLANG_EVIDENCE_DESK_0.1.1_20261101.zip
```

The app opens at `http://127.0.0.1:8765` on your computer. Choose the separate release ZIP you want to inspect. This is a local app, not the public project website. Press Ctrl+C in PowerShell to stop it. If port 8765 is already in use, extract the app ZIP and run `python .\evidence_desk.py --port 8766` from its folder.

**The local audit needs no API key.** The optional Gemini explanation is a real provider request and may be billable. See [the project page](https://reggaesharkk.github.io/sharklang-evidence-desk/) for a short overview and [the evaluation terms](EVALUATION_LICENSE.txt) before use.

## Checks and limits

- ZIP CRC/readability without extracting or executing files.
- Absolute and traversal paths, duplicate names, case collisions, symlinks, and encrypted entries.
- SHA-256 manifest matches, missing or mismatched files, and unlisted files.
- Heuristic credential patterns in supported text files up to 1 MiB each, plus credential-like filenames.

The report keeps test execution and proof checking **OPEN**. A matching checksum shows that bytes match a manifest; it does not establish that the code is safe, that tests passed, or that a theorem is correct. The credential scan can miss secrets and flag harmless examples. The tool does not execute tests, compile Lean proofs, validate theorem statements, audit legal rights, or prove a release secure.

## Optional Gemini explanation

If I click **Explain with Gemini**, the running terminal asks for `GEMINI_API_KEY` with hidden input. The app sends only aggregate counts and status labels to Gemini through the bundled SharkLang v2.4.2 egress client and a temporary local Witness. It does not send the ZIP, paths, file names, contents, or detected secret values. The app does not save the key. The local Witness demonstrates a request flow; it is not an independently administered production approval service. Provider usage may be billable, and this app sets no spending limit.

## Rights and citation

All rights are reserved. Inspection and non-commercial evaluation are allowed only under the included `EVALUATION_LICENSE.txt`. Production or commercial use, product or service integration, and redistribution require my written permission or a separate paid license. Bundled SharkLang runtime material and third-party works remain subject to their own notices and terms.

**Suggested citation:** Upadhyay, P. (2026). *SharkLang Evidence Desk* (Version 0.1.1) [Computer software]. GitHub: `reggaesharkk/sharklang-evidence-desk`. Zenodo record to be added when deposited.
