# LEDGER (append-only)

Claims and status changes, failed approaches with root causes, corrections, integrity events. Never edit an earlier entry; append a correction that references it.

## 2026-10-30 · integrity event · CI judge defined
- `.github/workflows/lean.yml` created: job `work` builds the `Work` library (sorry allowed); job `checked` builds `Checked` with axiom-audit (allowlist propext, Classical.choice, Quot.sound), leanchecker and nanoda (sorry not allowed).
- Status: UNTESTED. Must pass positive controls (annex 39.6) before any result is called PROVED.

## 2026-10-30 · governance · annex v3.0 → v3.1
- Added 40.0 (full fidelity audit applies to headline statements and definitions, not helper lemmas), a results-first preference in 42.1, "Physlib formatting only when preparing a contribution" in 47.1, and LIII (pace and accountability: 2-run target pick, 3-run first milestone, daily review, 24-run stall rule, short records).
- Reason: Alexander asked for a review aimed at results, not strategy. These cut audit and formatting overhead and add deadlines that turn 12 runs a day into results.
- Added CONSTITUTION_COMPLETE.md (all parts in one file) and governance/SHA256SUMS.

## 2026-10-30 · integrity event · lake-manifest.json added
- First CI run (40965992094) failed before building: lean-action requires `lake-manifest.json`, and Lean could not be run locally to generate it.
- Fix: copied Physlib's manifest (same toolchain, Mathlib v4.35.0 at 56a005855ea17e0b0958f73ec801ae140b0a1679, which matches the v4.35.0 tag; all other packages are Mathlib's own pinned dependencies) and renamed the package. No check was changed.

## 2026-10-30 · integrity event · nanoda moved to own step
- CI run 40966121805: `work` green; `checked` built and passed leanchecker, then lean-action's built-in nanoda step failed because it could not detect a module name from our lakefile (it expects a `[package]` table and exports the package-named module). axiom-audit was skipped as a result.
- Fix (commit b4dbb86): nanoda disabled inside lean-action and run by `scripts/nanoda_checked.sh` on module `Checked`, same tools and settings as lean-action v1.7.0 (permitted axioms incl. Lean.trustCompiler, non-hard error). nanoda acts as the independent type checker; axiom-audit remains the axiom judge with the strict allowlist. No check weakened relative to the intended design.

## 2026-10-30 · integrity event · nanoda report-only (known gap)
- CI run 40966663174: lean-action step green, including leanchecker and axiom-audit ("audited 1 declaration(s) under 'Checked'; all within the allowlist"). nanoda failed with "invalid digit found in string" while parsing the 13.8M-line export: the current lean4export output format and nanoda_lib's `debug` branch don't match for Lean v4.35.0. This is a tooling incompatibility, not a problem with our proofs; lean-action's own nanoda step would hit it too.
- Change: nanoda step set to `continue-on-error` (report-only). Blocking checks are now: build, leanchecker (kernel replay), axiom-audit (strict allowlist), forbidden-token grep.
- Open: repair nanoda (e.g. pin a lean4export revision that matches nanoda_lib) and make it blocking again. Low priority versus results; do it when a run has spare capacity or before any result is reported as a finding.

## 2026-10-30 · S1 complete · the judge works
- main @ 6-commit head: CI run 40967111191 green (work + checked: build, leanchecker, axiom-audit).
- Positive control 1, branch `control/sorry-in-checked`: run 40967115479 FAILED as required; axiom-audit reported `Checked.control_false_claim → [sorryAx]`.
- Positive control 2, branch `control/axiom-in-checked`: run 40967118310 FAILED as required; axiom-audit reported `Checked.control_uses_axiom → [Checked.control_bad_axiom]`.
- Both caught by axiom-audit inside the lean-action step, before the grep backstop ran. Branches kept, not merged.
- Remaining judge gap: nanoda report-only (see entry above).
