# LEDGER (append-only)

Claims and status changes, failed approaches with root causes, corrections, integrity events. Never edit an earlier entry; append a correction that references it.

## 2026-10-30 · integrity event · CI judge defined
- `.github/workflows/lean.yml` created: job `work` builds the `Work` library (sorry allowed); job `checked` builds `Checked` with axiom-audit (allowlist propext, Classical.choice, Quot.sound), leanchecker and nanoda (sorry not allowed).
- Status: UNTESTED. Must pass positive controls (annex 39.6) before any result is called PROVED.

## 2026-10-30 · governance · annex v3.0 → v3.1
- Added 40.0 (full fidelity audit applies to headline statements and definitions, not helper lemmas), a results-first preference in 42.1, "Physlib formatting only when preparing a contribution" in 47.1, and LIII (pace and accountability: 2-run target pick, 3-run first milestone, daily review, 24-run stall rule, short records).
- Reason: Alexander asked for a review aimed at results, not strategy. These cut audit and formatting overhead and add deadlines that turn 12 runs a day into results.
- Added CONSTITUTION_COMPLETE.md (all parts in one file) and governance/SHA256SUMS.
