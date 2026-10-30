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

## 2026-10-30 · governance · annex v3.1 → v3.2 (LIV, ever-improving)
- Alexander's standing instruction: the program improves itself; when it notices a fundamental issue or a repeated pattern it studies and fixes it; he should never need to replace the scheduled task's prompt.
- Added annex LIV (duty to fix, daily pattern hunting, what runs may and may not change, every change logged as an experiment and evaluated later, stored prompt never needs replacing), a matching block in the operative core, and item 7 in PROMPT.md. Scheduled task prompt updated once, from the setup chat, to say the program maintains its own instructions.
- How to tell if it works: patterns logged in LEDGER get fixes within a run or two, and later runs record whether each fix helped.

## 2026-10-30 · run 2026-10-30T0028Z · S2 · target 1 picked
- Target 1: cosmographic low-redshift expansions (TARGETS.md #1). First milestone frozen at 6ef1003.

## 2026-10-30 · claims · two PROVED
- `Checked.Cosmography.lookback_second_order` STATED (6ef1003) → AUDITED (runs/2026-10-30T0028Z/audit.md) → PROVED (CI 40981530819, 40982411889; axiom-audit 12 decls within allowlist; leanchecker ok).
- `Checked.Cosmography.lookback_second_order_bigO` STATED (e5b5372) → AUDITED → PROVED (CI 40982411889).
- Blind restatement disagreement (o(z²) under C² vs O(z³) under C³), classified Underspecified; resolved by proving both; the blind statement verbatim is derived in Lean.

## 2026-10-30 · candidates · literature screen
- 9 cosmography papers, 105 printed formulas screened with sympy; 4 papers with candidate coefficient errors (FINDINGS.md C1–C4). UNVERIFIED: transcription through a summariser is the main alternative explanation. Not reported to Alexander as findings.

## 2026-10-30 · experiment (annex LIV) · local Lean via elan
- Problem: setup chat could not install Lean; every check would go through ~3-min CI round trips. Root cause: environment of that session refused the installer. This scheduled environment allowed it.
- Change: STATE.md records the exact install commands; runs use local Lean for iteration, CI as the judge.
- Expected effect: proof iteration in ~30 s instead of ~3 min. How to tell: next runs record whether the install works and how many CI pushes a milestone needs.

## 2026-10-30 · experiment (annex LIV) · minimal imports in Checked
- Problem: `import Mathlib` in a Checked file made the nanoda export step exceed 10 min (export of all of Mathlib). Root cause: nanoda/leanchecker work scales with the import closure.
- Change: Checked files import specific modules (Checked/Cosmography/Lookback.lean: 4 modules); Work files may import Mathlib. Recorded in PROMPT.md.
- Effect seen: CI run 40982411889 finished in 4 min (vs > 9 min for 40981530819). Keep.
