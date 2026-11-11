# Run 2026-11-11T0028Z (scheduled)

**THE RESULT:** part 1 (rotation: part 1 had no landed progress since run 2026-11-09T0628Z) — statement fidelity T2b: which hypotheses of each headline actually matter is now machine-checked for 126 more hypotheses, and the classification can no longer silently regress (new blocking check).

**What can a scientist now trust without checking it themselves, that they could not before?** For 22 headlines (0 before) every hypothesis is machine-shown to be either needed (a Lean counterexample when it is dropped) or redundant (the statement proved without it), so no hypothesis of those theorems is decorative or silently doing the work; across all headlines 304 of 843 hypotheses are classified (178 before). And a classification, once shown, is now protected: CI fails if a witness disappears or a headline is renumbered so that a needed hypothesis becomes open again.

**Weakest unchecked step behind the results:** 539 hypotheses are still open — above all the boundary-value conditions (`f 0 = 0`, far-field limits) of the fluid-mechanics windows and the smoothness hypotheses (`ContDiffAt`) of the cosmographic series, whose counterexamples need solutions of perturbed problems (existence) rather than explicit functions.

**Measure:** TRUST_MAP.md — NEEDED 161 → 253, REDUNDANT 17 → 51, open 665 → 539, fully classified headlines 0/150 → 22/150.

## Start
- 00:28Z. LOCK of run 2026-11-09T2228Z found (last heartbeat 2026-11-09 23:36Z, ≈ 25 h; no push since 115b29e). Taken over by rule 48.4. Two consecutive runs (2028Z, 2228Z) took the LOCK and ended without records; no run pushed on 2026-11-10.
- Local Lean: elan installer ran (toolchain via lean-toolchain).
- CI read: run 42721774680 of 115b29e (descendant of the P13 records 6ba0381 and the β = −1/10 promotion c143ec5) green on every job, incl. the checked job (Lean step 3 h 07 min) and nanoda 4/4 (memoised). So the four β = −1/10 headlines are PROVED and P13 is live.
- Why no run on 2026-11-10: the account's scheduled-task list shows another routine's run of 2026-11-10 failing with USAGE_LIMIT_REACHED; the formalization runs of that day did not run, and runs 2028Z/2228Z of 11-09 most likely ended the same way (cut off mid-run, no records). Consequence for how runs work: a run can end at any moment without warning, so work must be pushed as it becomes green, not at the end.

## Work
- Finished run 2228Z's scratch batch (`runs/2026-11-09T2228Z/lean/NecessityB.lean`: 11 compile errors, all small) and added four families written this run (scratch in `lean/`, each compiled against the built modules while the full build ran):
  - **cubic equations of state**: at a pole of the isotherm (v = b, or a zero of the attraction denominator) neither the isotherm nor its derivative is differentiable, so both of Lean's junk derivatives are 0 and the critical-point condition holds there (`crit_of_unbounded`); the claimed constants then fail → `0 < b`, `b < v` needed in the vdW/RK/PR constants, hypotheses 2, 3 needed in `isCritical_iff` (8);
  - **cosmography model laws**: de Sitter violates the ΛCDM/CPL coefficient formulas and the records built on them; at Ω = 1 every flat CPL model has the printed fifth coefficient, so the condition (1 − Ω)(7 − Ω)wₐ ≠ 0 is needed (9);
  - **lookback expansions**: `a t₀ ≠ 0` redundant (zero scale factor: redshift −1, Hubble rate 0, remainder t₀ − t), `deriv a t₀ ≠ 0` needed (scale factor 1 + t²) (4);
  - **Hubble-rate family**: `a t₀ ≠ 0` is implied by `hubble a t₀ ≠ 0` in Lean (x/0 = 0), so redundant in 24 series headlines (one generic tactic); `hubble a t₀ ≠ 0` needed in 7 series headlines (1 + t²: the remainder is minus the series, of exact order x; `not_littleO_core`); the static model for `printedD2y_fails` (1).
- **New blocking check** `scripts/trust/check_necessity.py` (N1–N3, planted controls) with the baseline `scripts/trust/necessity_open_baseline.txt`; wired into the trust and frozen steps of `lean.yml`.
- **Adversary** (Sonnet, ≈ 1.5 min, on the first draft): 7 holes — (1) duplicate short names overwrite each other in the parser; (2) heading and totals found by substring anywhere (a rendered headline name could hijack them); (3) N2/N3 silently skipped on an unreadable base; (4) LEDGER disclosure matched any namespace and needed no indices, whitespace edits counted as added lines; (5) removed headlines and reclassification to "no obligation" invisible, N3 compensable; (6) baseline only mirrors TRUST_MAP (by design: N2 is the ratchet); (7) silent drops of unparsed lines, crash paths. All but (6) repaired with a control each before the step went live.

## Local checks (this tree)
- Full `lake build Checked` (≈ 78 min from the Mathlib cache, 2 cores) and the incremental build with NecessityB green; `StatementDeps.lean` (relock: new `NCB` doc entries only) and `Claims.lean` exit 0; CLAIMS.md, PHRASE_LINES.md unchanged; every Python check of the trust step green incl. `check_necessity.py` with `--base 115b29e`; `make_packet.py --check` green.

## Lessons
- One lemma per *kind* of hypothesis beats one witness per headline: junk division made 24 hypotheses redundant with one tactic line, junk derivatives at a pole made 8 needed, a single scale factor 1 + t² made 11 needed.
- A run can be cut off at any moment (usage limit): push compiled scratch immediately; the next run can then finish it (as this run did with 2228Z's).
