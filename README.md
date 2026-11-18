# Formalization

> **Unchecked prose.** This file is written by hand; no script checks what its sentences claim. What is machine-checked: the Lean statements in `Checked/`, their docstrings as far as `scripts/trust/check_prose.py` reads them, `TRUST_MAP.md` (generated), `CLAIMS.md` (every headline's claim generated from its Lean statement: rely on it, not on docstrings) and the certified numbers of `FINDINGS.md` (tagged ✓). When this file and those disagree, those win. **Statuses written here (PROVED, withdrawn, …) are hand-written too: a headline's status of record is the generated Status line under it in `CLAIMS.md` (a headline listed there is proved in `Checked` with the axioms shown; a withdrawn headline is not listed).** **Read what a headline claims on `CLAIMS_READER.md`: the generated claims, Status lines and fidelity records of `CLAIMS.md` with no author prose on the page.**

Alexander's program for making physics machine-checkable in Lean 4, run by scheduled Claude sessions.

- What's happening now: `STATE.md`
- What each run did: `CHANGELOG.md`
- Rules, all in one file: `CONSTITUTION_COMPLETE.md` (canonical separate parts in `governance/`)
- Instructions for the next run (edit any time): `PROMPT.md`
- What each result claims, generated from its Lean statement (run 2026-11-04T2228Z): `CLAIMS.md`
- The verified findings, generated from their Lean records with no author prose (run 2026-11-15T1628Z): `VERIFIED_FINDINGS.md`
- Results that passed the checker: `Checked/`
