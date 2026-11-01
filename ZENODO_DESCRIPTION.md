# Zenodo deposit draft

## Title

SharkLang Evidence Desk 0.1.1: Local Release ZIP Auditor

## Description

SharkLang Evidence Desk is a local evaluation prototype for inspecting research and software release ZIP archives before review. It reads the archive in place without extracting or executing its contents. Checks include ZIP readability and CRCs, unsafe or colliding paths, encrypted entries, SHA-256 manifest matches and omissions, and heuristic credential-pattern flags in supported text files.

The audit is intentionally bounded. A matching checksum shows that bytes agree with a listed manifest entry; it does not establish that the program is safe, that its tests pass, or that a mathematical claim is correct. The tool does not execute tests, compile Lean proofs, validate theorem statements, establish legal rights, or prove a release secure. Credential-pattern scanning can miss secrets and can flag harmless examples. Test and proof replay therefore remain OPEN.

The local audit works without an API key. An optional Gemini explanation sends aggregate counts and status labels only; it does not send the archive, paths, filenames, file contents, or detected secret values. Provider usage may be billable. The local Witness flow demonstrates a request path and is not an independently operated production approval service.

This release is provided for inspection and non-commercial evaluation under the included EVALUATION_LICENSE.txt. Production use, commercial use, product or service integration, and redistribution require separate written permission or a paid license from the rights holder. Third-party and bundled runtime material remains subject to its own notices and terms.

## Creators

Prince Upadhyay — independent researcher, India — ORCID: 0009-0002-1170-4487

## Suggested keywords

SharkLang; release verification; software artifact review; SHA-256; reproducible research; AI governance; security review; evidence boundaries

## Suggested version and date

Version 0.1.1 · 1 November 2026

## Rights metadata

Use Zenodo's **Add custom** license option with the title **SharkLang Evidence Desk Evaluation License 1.0**. State that all rights are reserved except the limited non-commercial evaluation permission in the attached `EVALUATION_LICENSE.txt`; production/commercial use, integration, and redistribution require separate written permission or a paid license. Do not accept Zenodo's default CC BY license for this deposit. Link to the license file after the GitHub repository is public: https://github.com/reggaesharkk/sharklang-evidence-desk/blob/main/EVALUATION_LICENSE.txt

Add the GitHub repository URL to the record metadata: https://github.com/reggaesharkk/sharklang-evidence-desk
