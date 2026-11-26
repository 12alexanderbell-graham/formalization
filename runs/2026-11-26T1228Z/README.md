# Run 2026-11-26T1228Z

**THE RESULT:** part 1 by rotation (STATE 3r; next step STATE 3s). The Lean theorems of this run and their statements are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For five statements on the boundary-layer equation with a pressure gradient against the flow (the largest wall shear, the bound on the wall shear at minus one tenth, the uniqueness of the separation value, the record of the separation value of the source and the bound below it), that ten of their wall and decay conditions are needed, by kernel theorems (section What we did; `TRUST_MAP.md`): each one dropped, certified solutions break the conclusion.

**Weakest unchecked step:** the sixteen hypotheses still open in `TRUST_MAP.md`, among them the positivity of the second derivative in all five of these statements (section Next).

## Start
- 12:28Z. Local `main` was the stale shallow clone 860fd46; after deepening, it was an ancestor of origin/main and fast-forwarded to fe66f1c; `scripts/start_run.sh` (no LOCK); LOCK taken 86d605f (48.4).
- Env: repo ok (add_repo not exposed; the session clone was present; push works). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of a53280d (artifact of 45809568668) restored by streaming; `lake build Checked` replayed it. No subagents.
- CI read first: no push with Lean or check changes after a53280d (fe66f1c and 84d67bd are records only); 45809568668 of a53280d was read green on every job by run 1028Z. Newest ancestor green on every job: a53280d.

## What we did

Section Next of run 0628Z: hypotheses 13 (`f₂ 0 = 0`) and 16 (`q₂ > 0`) of `fs_neg_decay_max_shear`, both "needing a solution no certified module has" (13: a suction start). Runs 2026-11-14T0228Z, 2026-11-15T1428Z and 0628Z had each named the suction start as the blocker; the PROMPT note of run 2026-11-11T2228Z already said a stack ports to a free start by asserted replacements. This run did that for both adverse-gradient stacks and a moving wall.

1. **The second solution need not approach fast** (scan `scripts/scan_h13.py`, floating point, not evidence). For β < 0 the problem has a one-parameter family of solutions with p → 1; a slow-approach trajectory (event `SlowA`) is one. So hypothesis 13 needs no shooting: a slow trajectory from the suction start (C, 0, α) with a large enough α. At K = 10 (β = −1/10) the scaled start (1/20, 0, 21/20) is slow (shooting value about 1.44 there, against 1.0096 without suction), and its wall shear 21/20/√10 ≈ 0.332 exceeds the attached bound 0.3192697599 of `fs_neg_tenth_window`.
2. **Suction port of the attached stack** (`Checked/FSAtt/Suction.lean`, written by `scripts/mk_suction.py` from `AFlow`, `AUnclamp.unclamp`, `AAssemble.slow_class` by asserted replacements; compiled first time): `flowC K C α` from (C, 0, α), `ChainC`, `unclampC` (0 ≤ C ≤ 2: f ≤ t + C keeps the clamp |f| ≤ t + 2 inactive), `slow_classC` (f 0 = √K·C). Chain `Checked/FSAtt/SuctionSlow.lean` (`scripts/gen_suction.py` = `gen_neg_wc_theta.py` with `FS_C`, `scripts/emit_suction.py`; 54 cells, L = 3/2, path margin 0.027, end margin 0.26).
3. **`Checked/Trust/NecessityCD.lean`**: `suction_tenth`, `fs_neg_decay_max_shear_h13` (with the attached solution of `fs_neg_tenth_exists_decay`) and `fs_neg_tenth_monotone_lt_h4` (the same solution: `fs_neg_tenth_monotone_lt` asks no fast approach either).
4. **Separation stack at a suction start and at a moving wall** (`scripts/scan_sep_suction.py`, `scan_sep_wall.py`): the separation value moves fast with the start (scaled K* = 5.0292 without; 5.0080 at suction 1/1000, below 5 already at 3/1000; 5.0152 at wall velocity 1/1000), and the stack needs K ≥ 5, so both offsets are one thousandth. `Checked/FSSep/SuctionSep.lean` (`scripts/mk_sep_suction.py`) and `Checked/FSSep/WallSep.lean` (`scripts/mk_sep_wall.py`): `SFlow` (flow continuous in K), `SUnclamp` (start, slow and no-event unclamping), `SAssemble` (openness, no-event class, shooting core with the chain coefficients as parameters: `core_sepS`, `core_sepW`) ported by asserted replacements; only one replacement needed a fix (a structure field renamed by the qualifying regex). Chains (`scripts/gen_sep_suction.py` = `gen_sep_wc.py` with `FS_C`, `FS_P`; `emit_sep_suction.py`, `emit_sep_wall.py`; 192 cells each, L = 6): `SuctionSepOver` (K = 5007/1000), `SuctionSepSlow` (5009/1000), `WallSepOver` (5014/1000), `WallSepSlow` (5016/1000); all compiled first time.
5. **Slow separation trajectory above the printed value**: `Checked/FSSep/SSlowFiveThree.lean` (the original generator at K = 503/100, L = 3, 96 cells; `scripts/emit_sep_slow503.py`) and `SSlowSol.slow_sol` give a solution with zero wall shear, p → 1 and q > 0 after the wall at β = −100/503 ≈ −0.198807, above the printed −0.1988376, without the fast approach.
6. **`Checked/Trust/NecessityCE.lean`**: `suction_sep` (β < −0.1996), `wall_sep` (β < −0.1993), `slow_sep`; `fs_separation_equal_h4`, `_h13` (suction, either solution), `_h5`, `_h14` (moving wall), `F12_separation_h4`, `_h5`, `_h9`, `fs_separation_below_printed_h9`.

Axioms of all ten necessity theorems: propext, Classical.choice, Quot.sound (`lake env lean` of an axiom print).

## Measure

- Trust map (StatementDeps relock): NEEDED +10, open 26 → 16 (`fs_neg_decay_max_shear` 13; `fs_neg_tenth_monotone_lt` 4; `fs_separation_equal` 4, 5, 13, 14; `F12_separation` 4, 5, 9; `fs_separation_below_printed` 9); `scripts/trust/necessity_open_baseline.txt` shrunk in the same commit.
- Pipeline cost: about ten minutes per witness family from scan to compiled theorem; every port and chain compiled first time except one regex slip. Hypothesis 13 had waited twelve days on "no certified module has a suction start".

## Next
- CI read first: the run of this run's final push (new Checked modules `Suction`, `SuctionSlow`, `SuctionSep`, `SuctionSepOver`, `SuctionSepSlow`, `WallSep`, `WallSepOver`, `WallSepSlow`, `SSlowFiveThree`, `NecessityCD`, `NecessityCE`). Green on every job → nothing to promote (necessity theorems only). Red → `python3 scripts/trust/records_check.py <base>` with the newest ancestor green on every job (a53280d).
- Part 1 next: the blowing and receding-wall witnesses (`fs_separation_below_printed` 4 and 5 need a separation value above the printed one, so f(0) < 0 or p(0) < 0; the unclamping uses f ≥ 0 and p ≥ 0, so the port needs an energy bound that tolerates a small negative f near the wall), then the positivity hypotheses (`fs_neg_decay_max_shear` 16, `fs_neg_tenth_monotone_lt` 7, `fs_separation_equal` 8 and 17, `F12_separation` 8, `fs_separation_below_printed` 8): an overshoot that returns to one (plan in section Next of `runs/2026-11-26T0628Z/README.md`).
- Part 3 next: as in section Next of `runs/2026-11-26T0828Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-26T1028Z/README.md` (the H₂⁺ ground state first).

## End
