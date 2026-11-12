# Run 2026-11-12T1628Z (scheduled)

**THE RESULT:** part 1 by rotation (trust layer: hypothesis necessity) — 24 hypotheses of eleven Falkner–Skan headlines classified by machine-checked witnesses (13 REDUNDANT, 11 NEEDED); plus a CI root-cause repair that unblocks every main checked job (part 1 infrastructure).

**What can a scientist now trust without checking it themselves, that they could not before?** For the adverse-pressure-gradient Falkner–Skan claims (the β = −0.1, −0.17, −0.18, −0.19, −0.1988 wall-shear windows, the separation value and its printed-value refutation, the decay-class uniqueness pair), the edge condition f' → 1 is shown by Lean to follow from the other assumptions (so it is not carrying the result), while the coupling p' = q and, where a reverse-flow solution is certified, positivity of the shear are shown to be needed — the latter means the decay class alone does not pick the attached branch.

**Weakest unchecked step:** f(0) = 0, p(0) = 0 and the decay class are still open in these headlines (witnesses need certified suction or moving-wall solutions at β < 0); q > 0 is open at the three Ganapol rows (no reverse-flow solution certified there). Today's promotions (NegWallShearRows, F12–F14) are not yet judged by a green checked job.

## Start
- 16:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main (54/72 diverged; kept as local branch `stale-local-main-backup`); `git fetch --unshallow` + `git checkout -B main origin/main` = 156c3da. No LOCK on origin/main → LOCK taken (9dc6138).
- Local Lean: elan + Mathlib cache (≈ 3 min); CI artifact `checked-build` of 43196172253 (0e262e6) restored (`pip install zstandard`); incremental `lake build Checked` ≈ 12 min (run 1428Z's certificate modules).
- Bottleneck (part 1 by rotation, STATE next step 0): the open hypotheses of the FS window headlines. A yes changes what a reader may ignore in nine-plus claims; a no would say which of them carry the result.

## CI read
- 43218463622 (4c7b118, run 1028Z's records F12–F14): every job green except **checked (strict), cancelled at its 240-min limit**. Job log (131183812627): lake cache miss → Checked build 97 min, leanchecker 47 min, then the axiom-audit step's bare `lake build` rebuilt all of Work single-threaded (still building at 90 min). Same signature as f789e4d's 4-h hang. 0e262e6 had passed only because its cache held Work (audit 34 s).
- **Repair:** `lakefile.toml` `defaultTargets = ["Checked"]` (LEDGER). 43252958184 (156c3da, run 1428Z's final push) cancelled by hand: its checked job would have repeated the timeout; this run's push descends from it and is the next judge of 1428Z's and 1028Z's promotions.

## Work
1. `Checked/Trust/NecessityR.lean` (namespace `Checked.Trust.NCS`; scratch `lean/NecessityR.lean` compiled first try apart from three renamed Mathlib lemmas):
   - `lim_one`: β ≤ 0, f' = p, p' = q, the equation, q ≥ 0 and the decay class ⇒ p → 1. p is increasing; if it stayed ≤ a < 1, the class with M = 1/(1 − a) gives q ≥ 1 eventually and p would be unbounded; if it reached b > 1, f is eventually positive, the equation makes q' ≤ −f q ≤ 0, but the class with M = −(q(η₁) + 1)/(b − 1) forces q above its earlier value.
   - `beta_nonpos`: at a separation profile (f(0) = p(0) = q(0) = 0, q > 0 to the right) the equation gives q'(0) = −β, and the slope limit gives β ≤ 0; so `lim_sep` covers the separation headlines.
   - Witnesses: `*_r6` (six windows), `fs_neg_decay_max_shear_r7`, `fs_neg_decay_equal_r7/_r15`, `fs_separation_below_printed_r7`, `F12_separation_r7`, `fs_separation_equal_r7/_r16`; `*_window_h2`, `F13_wall_shear_h2` (velocity `min η 1`, stream function its primitive, shear q = e^{−G}(1 − β∫e^{G}(1 − p²)), G = ∫f, wall value one); `fs_separation_equal_h2/_h11`; `fs_neg_tenth_window_h7`, `fs_neg_wall_shear_window_h7`, `F13_wall_shear_h7` (the certified reverse-flow solutions satisfy the decay class).
   - Namespace first written as `NCR`, which `Checked/Trust/NecessityG.lean` already uses (no clash of names, but confusing): renamed `NCS` before the relock.
2. StatementDeps (relock): needed 472 → 483, redundant 127 → 140, open 331 → 307 (930 hypotheses of 160 headlines); fully classified unchanged (56: none of the eleven is complete yet).

## Local checks and push
- (filled below)

## Next start
- CI read first: this run's final push (first main run with the lakefile repair). Green on every job → NegWallShearRows (1428Z) and F12–F14 (1028Z) PROVED; tell Alexander in one L.2 message (F12–F14 + Bonnor–Ebert, if not sent). Read the checked job's step times (expected ≈ 3 h uncached).
- Part 1 next: f(0) = 0 / p(0) = 0 at β < 0 (port `Checked/Suction/` to the attached K-stack), q > 0 at the Ganapol rows (reverse-flow chains, `Checked/FSRev/` generator), the decay class (an algebraically decaying attached solution).
