# Run 2026-11-19T1828Z

**THE RESULT:** part 1 by rotation (STATE 2b → part 1 as in section Next of `runs/2026-11-19T1228Z/README.md`, trust track T2b). Ten hypotheses of listed statements are shown NEEDED by Lean theorems with certified counter-examples (section What we did).

**What can a scientist now trust without checking it themselves, that they could not before?** For ten more hypotheses (the conditions at the wall of six boundary-layer statements), a Lean theorem that the statement fails without each of them; four of the six statements now have every hypothesis classified.

**Weakest unchecked step:** the hypotheses still listed open in `TRUST_MAP.md` (section Next).

## Start
- 18:28Z. Local main was a stale divergent clone; `git checkout -B main origin/main` at 1b242fe. No LOCK → taken (aa6614a).
- Local Lean: elan + `lake exe cache get` ≈ 2 min; `checked-build` of 44577216209 (1b242fe, 2.7 GB) restored with DELETE_ZIP=1 (3 GB free afterwards; `~/.cache/mathlib` deleted).
- CI at start: 44577216209 (1b242fe, promotion of `laneEmden52_constants`): the checked job green (18:11Z), leanchecker 4/4 green (by 18:43Z), nanoda shard 0 green (18:41Z), nanoda shards 1–3 running.

## Bottleneck (and what a yes/no changes)
- Part 1 (T2b). Run 2026-11-11T2228Z's experiment asked whether the remaining wall and initial conditions of shooting headlines fall to the parametrised-start route (certified cells from a perturbed start). Open for eight days: hypotheses 5 (f(0) = 0) and 6 (p(0) = 0) of the four Hiemenz/Homann shooting statements `hiemenz_under`, `hiemenz_over`, `homann_under`, `homann_over`, and 5 of the two monotone windows. Yes → ten hypotheses classified with the existing cell checker (`HCellWC`, `HmCellWC`) and no new mathematics; four headlines fully classified. No → the overshooting starts leave the clamps and need a new clamped field.

## What we did
- **Float scan first** (`scipy`, not evidence): for the overshoot statements a start with f(0) = 1/10 or p(0) = −1/20 (Hiemenz), −1/10 (Homann) at the upper wall shear of the bracket keeps p < 1 on the whole window and stays inside the clamps (|f| ≤ η + 2, |p|, |q| ≤ 2); for the undershoot statements a start with f(0) = −1/100 or p(0) = 1/100 (Hiemenz), −1/50 or 1/50 (Homann) at the lower wall shear keeps q > 0 on the whole window, also inside the clamps (larger perturbations overshoot past p = 2 before the end of the window).
- **Certified cells on the whole window** (`scripts/gen_hiemenz_wc_sp.py`, `scripts/gen_k_wc_sp.py`: the run-2026-11-11T2228Z generators with the start velocity `FS_P` added; `scripts/emit_hz_wall.py`): eight modules `Checked/Trust/HzWall{S,P,US,UP}.lean` (60 cells, h = 1/8, on [0, 15/2]) and `HmWall{S,P,US,UP}.lean` (96 cells, h = 1/16, on [0, 6]), each with `chainP` (p < 1 throughout) or `chainQ` (q > 0 throughout) and `boxC` (every clamp inactive, the `HIVP` pattern). Every side condition kernel-decided; ≈ 40–55 s per module locally.
- **Witnesses** (`Checked/Trust/NecessityBA.lean`): a clamped solution on the window from any start (Picard–Lindelöf, `ncba_local_sol`, `ncba_local_solHm`) equals the unclamped field inside the clamps (`ncba_solves`, `ncba_solvesHm`); with `chainP` it never overshoots (`hiemenz_over_h5`, `_h6`, `homann_over_h5`, `_h6`), with `chainQ` it never undershoots (`hiemenz_under_h5`, `_h6`, `homann_under_h5`, `_h6`).
- **Wall velocity in the monotone windows** (hypothesis 5 of `hiemenz_monotone_window`, `homann_monotone_window`; these need a solution on [0, ∞)): the suction stacks `Checked/Suction/{HS,HmS}{Flow,Limit,Assemble}` ported to a start (a0, b0, α) with 0 ≤ b0 < 1 by asserted replacements (`scripts/port_wallvel.py` → `Checked/Trust/{HzG,HmG}{Flow,Limit,Assemble}.lean`; the only proof changes: four uses of p(0) = 0 become 0 ≤ b0 < 1); certified shooting chains from (0, 1/10, α) on [0, 2] (`{HzG,HmG}{U,O}Data.lean`, `scripts/emit_wc_g.py`) at α = 1.1 / 1.2 (Hiemenz) and 1.18 / 1.28 (Homann); `exists_bvpG` gives a monotone solution with p(0) = 1/10, q > 0, p → 1 and wall shear below each window (`hiemenz_monotone_window_h5`, `homann_monotone_window_h5`). The port compiled after two fixes (the interval end written `2 / 1` as the stacks write it; `simp only [flowG_zero]` where `simp` rewrote 1/10 to 10⁻¹ first).
- Axioms of every new theorem: propext, Classical.choice, Quot.sound (StatementDeps).

## Measure
- Necessity (StatementDeps relock): NEEDED 709 → 719, open 89 → 79; headlines with every hypothesis classified 120/176 → 124/176 (`hiemenz_under`, `hiemenz_over`, `homann_under`, `homann_over`). Experiment of run 2026-11-11T2228Z (parametrised starts for the remaining wall/initial conditions): met for these ten; time ≈ 50 min from the first float scan to the last witness, no new mathematics.

## CI read
- See Start; final read below (End).

## End
- 19:2xZ. 44577216209 (1b242fe): nanoda shards 1–3 still running (since 17:38–17:41Z); not judged in this run. A float scan for hypothesis 6 (p → 1) of the monotone windows: above the window the solutions exist to η = 60 with q > 0 and p growing like e^{aη} (q(0) = 1.24: p(60) ≈ 730), so hypothesis 6 is likely NEEDED, but a Lean witness needs global existence without clamps.
- See the final commit message for the local checks run before the push.
- The final commit 88d46d6 carried only the LOCK removal (a `git add` that named the already removed LOCK aborted, and the commit ran anyway); the records followed in e42bd17 (final (2)), and the CI run of 88d46d6 (44598081581) was cancelled by hand (its tree had a stale relock and could not be green). Fix (annex LIV): `scripts/check_commit_msg.py --final` now also fails on unstaged tracked files or an empty index (controls: an unstaged change fails, the staged tree passes). The run to read for this run is 44598131615 (e42bd17).

## Next
- CI read first: 44577216209 (1b242fe, promotion of `laneEmden52_constants`) once nanoda shards 1–3 end, or the run of this run's final push (a descendant: ten new Trust helper modules, `NecessityBA`). Green on every job → `laneEmden52_constants` PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>` or `local_frozen_step.py --trust <base>`.
- Then by rotation (part 1 at 1828Z, parts 2/5 at 1628Z, part 3 at 1428Z): part 3 as in section Next of `runs/2026-11-19T1428Z/README.md`; parts 2/5 as in section Next of `runs/2026-11-19T1628Z/README.md`. Part 1 later: hypothesis 6 (p → 1) of the monotone and limit windows needs a global solution with q > 0 that does not tend to one (float scan first: exponential growth p ≈ C e^{aη} is consistent at leading order, so it may exist); the wall conditions of `fs_neg_reversed_printed_overshoots` (4, 5) and `fs_separation_below_printed` (4, 5) need a solution on [0, ∞), so the route of `port_wallvel.py` (a ported stack with a free start) is the candidate; `eta_ratios` 3, 4 and the B1 lower density bounds as in section Next of `runs/2026-11-19T1228Z/README.md`.
