# Run 2026-11-25T0028Z

**THE RESULT:** part 1 by rotation (STATE 2z; next step STATE 3a). The Lean theorems of this run are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** That every hypothesis of the new third-coefficient headline (`third_coefficient_lower_bound`) is either needed (a model and a cubic meeting all the others with a₃ at most thirteen fifths, checked in Lean) or redundant (the statement without it, proved): before this run six of its nineteen were unclassified; and, for the RL19 box statement, that it does not use the redshift of its nearest source and does use its expansion law (a scale factor without it, checked in Lean, has a box cubic matching all three sources).

**Weakest unchecked step:** the last open hypothesis of `rl19_box_unmatched`, 2 (the upper density bound): flat models with density up to twenty give no witness in floats, and a redundancy proof would have to cover every density above one (section Next); and, unchanged, the B1 statements are about three redshifts and a uniform window, not a fit to data with errors.

## Start
- 00:28Z. `scripts/start_run.sh`: local main = origin/main 860fd46; LOCK of run 2026-11-21T1828Z, last heartbeat 2026-11-21 19:52Z (four days; that run left no records) → taken over (177644f, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 3a2c1fc (artifact of 44939209059) restored by streaming; the container's disk allowance left 2 GB after the restore (pip and Mathlib download caches deleted). No subagents.

## CI read
- 44939209059 (3a2c1fc, run 1628Z's final push): every Lean job green (checked incl. trust step and relock, work, leanchecker 4/4, nanoda 4/4, packet). **The goal-guard job failed:** its LOCK rule ("the HEAD commit message says it removes the LOCK, but LOCK is still in the tree"): run 1628Z's final message said 'remove LOCK' while run 1828Z had taken the LOCK over (recorded in run 1628Z's README, section End). A records fault, not a proof fault; but "green on every job" is the PROVED bar, so `third_coefficient_lower_bound` stays "PROVED once a main run is green on every job" until the run of this run's push is read (section Next).

## Bottleneck (and what a yes/no changes)
- The new headline of run 1628Z entered with six open hypotheses (1, 2, 9, 10, 15, 17); open hypotheses are the trust map's measure of what a reader cannot yet rely on for a statement. Can all six be decided in one run? Yes → the headline is fully classified (its necessity record on the claims page has no open entry). No → which ones resist, and why, is recorded.

## What we did
- **Run 1828Z's unrecorded work recovered.** It had committed a generator (`runs/2026-11-21T1828Z/scripts/emit_om3.py`) and its output for hypotheses 2 and 9 (flat closed-form model `NCAQ.sa` at matter density three, rectangle sums of the three distance integrals, cubic a₂ = 1/4, a₃ = 13/5), never compiled in a run record. Copied to `runs/2026-11-25T0028Z/scripts/emit_om3.py` with only the module name and generated-by line changed (deterministic: its rerun reproduced 1828Z's file byte for byte before the change); output `Checked/Trust/NecessityBP.lean` compiled first time (≈ 2.5 min). **2 (Ω ≤ 1) and 9 (the expansion law) NEEDED.**
- **`Checked/Trust/NecessityBQ.lean` (this run):**
  - **15 (positivity at the middle source) REDUNDANT** by algebra alone: 25 B(3u) − 9 B(5u) = 30u − 450 a₃u³ (u = log₁₀2 / 2), so B(3u) ≤ 0 < B(5u) gives a₃ > 4/(15 λ²) ≈ 2.94 > 13/5 (`nbq_mid`). Run 1628Z's next step had planned it "as the `fit_direction` counterpart"; that proof uses the direction's conclusion, this one does not need the residuals at all.
  - **17 (residual at the nearest source) and 10 (its redshift) NEEDED**: Einstein–de Sitter (`NCAR.ea`), cubic a₂ = 50, a₃ = 13/5, H = 7.175, offset 0; both residuals within 2 % (`resid_band`; `runs/2026-11-25T0028Z/scripts/eds_a3.py` checks the conditions in exact rationals). A float scan shows why a₂ must be large: with a₃ ≤ 13/5 an exact match at the two farther sources forces a negative polynomial; only the 0.1-mag spread admits a positive one (spread 0.067 mag at a₂ = 50).
  - **1 (0 ≤ Ω) REDUNDANT**: the route of `NCBN.fit_direction_r1` copied by string up to its inequality 18κP₁ ≤ 0.42 P₅ (which does not use the conclusion), then two lines: with P₃ > 0 it gives Y > 0.9 log 2 for Y = a₃ log³2 / log²10, i.e. a₃ ≳ 10.
  - **`rl19_box_unmatched` 9 (the expansion law) NEEDED** (`Checked/Trust/NecessityBR.lean`): no flat ΛCDM model (density up to twenty) and no single power law brings a box cubic within 0.1 mag (best 0.19, Einstein–de Sitter); a float scan of two-piece power laws (`scripts/scan_r9.py`) found one at 0.044 mag: `cs` coasts (a = t) after the time where a = 5/9 and is √(10t/9 − 25/81) before it (same value and slope at the break, so differentiable: `cs_deriv_mid` by one-sided derivatives). Its distances are closed forms (`cs_d1` = √2 log 2 / 2, `cs_d3` = 2√2(1 + log 9/5) − 9/5, `cs_d5` = 4√2(1 + log 9/5) − 9/5, by the fundamental theorem on each piece); log 9/5 from six terms of the series of log 9/10 (`log95_bd`). Box cubic a₂ = 87/25, a₃ = 169/100, H = 1.1153, each ratio within 1.03 % of one. Compiled first time after four tactic repairs (≈ 15 min).
  - **`rl19_box_unmatched` 10 (redshift of the nearest source) REDUNDANT** (`rl19_box_unmatched_r10`): for Ω ∈ [0, 1] the integrand decreases, so J₅/J₃ ≥ (1 − w₅)/(1 − w₃) ≈ 1.4295 (`bq_ratio35`, `NCBL.bl_ratio13` with the indices moved by string); in the box B(5u) ≤ 2.65 B(3u) (`bq_box_ratio`, upper box bounds only); the residuals at the two farther sources (`ratio_step`) then force J₅/J₃ ≤ 1.3874. The nearest source plays no part.
- Axioms of every new theorem: those of the modules they import (propext, Classical.choice, Quot.sound; `lake env lean` of both files green; the CI judge rechecks).

## Measure
- `third_coefficient_lower_bound`: open 6 → 0 of 19 (needed 7 → 11, redundant 6 → 8). `rl19_box_unmatched`: open 3 → 1 (9 NEEDED, 10 REDUNDANT).
- Trust map (`TRUST_MAP.md`): NEEDED 767 → 772, REDUNDANT 249 → 252, open 42 → 34; non-vacuity 188/188; headlines 310.

## Local checks
- See section End.

## Next
- CI read first: the run of this run's push (new Checked modules `NecessityBP`, `NecessityBQ`, `NecessityBR`). Green on every job (goal guard included) → `third_coefficient_lower_bound` PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>`; a red goal guard → `python3 scripts/goal_guard.py`.
- Part 3 next: as in section Next of `runs/2026-11-21T1428Z/README.md`.
- Part 1 next: `rl19_box_unmatched` 2: flat models with density in (1, 20] give spreads 0.2–0.77 mag (no witness); if REDUNDANT, the proof must cover every density above one (the integrand then increases in v; the limit shape is ∫ dv/√(1 − v⁶)). Then the curved pair of `l19_sq_curved`, `l19_sqg_curved` (1, 8). **Method note:** when a hypothesis to drop is a law, the witness need not obey any law: a scale factor built from closed-form pieces joined with equal value and slope (here coasting and a square root) has closed-form distances and two free shape parameters (break and exponent), which a float scan fits in seconds; this beat ODE models (a closed model with Ωm = 3/2, Ωk = −5/2 also fits at 0.063 mag but has no Lean scale factor).
- Parts 2/5 next: as in section Next of `runs/2026-11-21T1628Z/README.md`.

## End
- Local: `lake build Checked` (restored build of 3a2c1fc; 3784 jobs), `lake env lean` of the three new modules (the third, `NecessityBR`, added after the first relock and `records_check`; relock and Claims rerun), `precheck_names.py`, `check_prose.py`, `check_necessity.py`, `check_stale_necessity.py`, `precheck_citations.py`, `check_status_lines.py`, `TRUST_RELOCK=1 … StatementDeps.lean` twice (final: 310 headlines, NV 188/188, necessity 772 / 252 / 34 open), `Claims.lean` twice, `records_check.py c7d06a1` (the newest ancestor green on every job; a first run with base 177644f0 flagged a pending status of `third_coefficient_lower_bound` for want of a green run, a false alarm of the wrong base: PROMPT note).
- The container restarted at ≈ 01:25Z and killed the second StatementDeps run; rerun with `setsid nohup` (≈ 29 min with cold file caches against ≈ 14 min before).
- Message to Alexander (L.2): none this run; the promotion of run 1628Z gets its L.2 line when a run green on every job is read (section Next).
