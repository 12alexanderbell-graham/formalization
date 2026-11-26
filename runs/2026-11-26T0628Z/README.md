# Run 2026-11-26T0628Z

**THE RESULT:** part 1 by rotation (STATE 3o; next step STATE 3p). The Lean theorems of this run and their statements are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For the statement on the largest wall shear of the boundary-layer equation with a pressure gradient against the flow, that its no-slip condition on the fast-approach solution is not decoration, by a kernel theorem (section What we did; `TRUST_MAP.md`): without it the conclusion is false, for a certified pair of solutions.

**Weakest unchecked step:** the two other open hypotheses of that statement (the wall value of the stream function of the second solution and the sign of its second derivative), still open in `TRUST_MAP.md` (section Next).

## Start
- 06:28Z. Local `main` was the stale clone 860fd46 (its commits are on origin branches); set to origin/main 6d99ea9, then `scripts/start_run.sh`; no LOCK (taken 9b41ccc, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 0f19e0a (artifact of 45763705693) restored by streaming; `lake build Checked` replayed it (3819 jobs). No subagents.
- CI read first: 45763705693 (0f19e0a, run 0428Z's final push) green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4) → `bonnor_ebert_turning_decay` judged PROVED (STATE heading, judged template).

## What we did

Section Next of run 0028Z: hypotheses 6, 13 and 16 of `fs_neg_decay_max_shear` (β < 0: a solution `f, p, q` with `f 0 = 0`, `p 0 = 0`, `p → 1`, `q > 0` and the fast approach, and a solution `f₂, p₂, q₂` with `f₂ 0 = 0`, `p₂ 0 = 0`, `p₂ → 1`, `q₂ > 0`, give `q₂ 0 ≤ q 0`), scanning 6 and 13 before choosing between a witness and a redundancy plan.

1. **Scans** (`scripts/scan_h6_h13.py`, `scan_h6_cross.py`, `scan_h6_095.py`, outputs `.out` beside them). The reversed-flow solution (`q 0 < 0`, fast approach) has its stream function return to zero at some η* after its velocity turns positive; translated to η*, it satisfies every hypothesis of the first solution except `p 0 = 0`. Its second derivative there is below the attached wall shear for β from −0.02 to −0.095 (margin +0.077 at −0.05, +0.0057 at −0.095) and above it at −0.1 and beyond: hypothesis 6 is NEEDED where the margin is positive. The attached chains of `Checked.FSAtt.AWindow` need a scaled wall shear at most 11/10, which holds for β = −19/200 (1.0645) and not for −0.09 (1.1225): the witness is at β = −19/200. Hypothesis 13 (`f₂ 0 = 0`): the same translation to the zero of the velocity gives blowing (`f₂ 0 < 0`) and a smaller wall shear (0.15 against 0.32 at −0.1), the wrong direction; a witness needs a suction solution (`f₂ 0 > 0`), which no certified module has.
2. **Certificates** (`scripts/make_h6_chains.sh`, rows `scripts/rows_h6.json`, cells in `cells/`; the existing generators `gen_rev.py` and `gen_neg_wc_theta.py`, all five chains OK in six seconds): reversed-flow over (A = −0.451…, L = 5, 166 cells), slow (L = 17/4, 142 cells), tube (L = 3/2, step 1/128, 192 cells, radius 4.8·10⁻¹¹); attached slow at A = 1063/1000 (134 cells) and over at 107/100 (166 cells). Emitted by `scripts/emit_h6.py`: `Checked/FSRev/RNinetyFive{Over,Slow,Tube,Zero}.lean`, `Checked/FSAtt/RNinetyFive{Lo,Hi}.lean` (each about two minutes in Lean; all compiled first time).
3. **New side condition** (`Checked/FSRev/RZero.lean`, `PhiZ`, `sideZ`, `sideZ_spec`): from a time `a` on, q > 0, and q < X wherever g ≤ 0; at `a`, g < 0. `RNinetyFiveZero` is the tube's cells checked again with it at a = 5/8, X = 53/50 (`scripts/check_sidez.py` evaluated it in exact rationals first: tightest margin 0.0020, at the cell from 85/64).
4. **Assembly.** `Checked/FSRev/RAssembleZ.lean` (generated from `RAssemble` by `scripts/mk_rassemblez.py`, asserted replacements): `core_revZ` names the solution as the scaled flow of the chosen shooting value and adds q > 0 from the tube's end on (the proof already had it as `hqpos`). `Checked/Trust/NecessityCB.lean`: `shifted_rev` (the zero t₀ of the scaled stream function in [5/8, 3/2] by the intermediate value theorem; translation by √K·t₀; derivatives by `HasDerivAt.comp_add_const`) and `fs_neg_decay_max_shear_h6` with the attached solution of `AWindow.core_window`: its scaled wall shear exceeds 1063/1000 > 53/50. Axioms: propext, Classical.choice, Quot.sound.

## Measure

- Trust map (StatementDeps relock): NEEDED +1 (hypothesis 6 of the largest-wall-shear statement), open 27 → 26; see `TRUST_MAP.md`.
- Pipeline cost: scan to compiled witness in about thirty minutes, because the generators, emitters and assembly lemmas of the reversed-flow and attached tables (runs 2026-11-11 to 2026-11-13) took a new coefficient unchanged; the only new Lean is one side condition (60 lines) and the assembly (110 lines).

## Next
- CI read first: the run of this run's final push (new Checked modules `RZero`, `RAssembleZ`, `RNinetyFive{Over,Slow,Tube,Zero,Lo,Hi}`, `NecessityCB`). Green on every job → nothing to promote (necessity theorems only). Red → `python3 scripts/trust/records_check.py <base>` with the newest ancestor green on every job (0f19e0a, read green in this run).
- Part 1 next: hypotheses 13 (`f₂ 0 = 0`) and 16 (`q₂ > 0`) of `fs_neg_decay_max_shear`, both NEEDED by scan, both needing a solution no certified module has. 16: an overshooting solution (q₂(0) above the attached value) with an analytic tail; the scan of this run (`scripts/scan_h16_handoff.py`) shows that just after the velocity maximum (η ≈ 4 at β = −0.1) the solution enters the region p > 1, q < 0, Z = q f + λ(p − 1) > 0 with f²(λ − b(p + 1)) > λ(p + λ) (b = −β, λ = 3b(p + 1)); there Z = 0 cannot be reached (Z′ > 0 on it), p − 1 stays positive (q ≥ −λ(p − 1)/f), q stays negative, and a limit above one makes f q bounded away from zero and p → −∞; but the clamp |F| ≤ t + 2 of `flowA` is crossed by every overshooting solution, so the tail also needs a global solution of the unclamped system (a new clamp, or existence from the a priori bounds). 13: a suction solution (f₂(0) > 0) of the attached class, which needs a flow started from (c, 0, α).
- Part 3 next: as in section Next of `runs/2026-11-26T0228Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-26T0428Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge's build of 0f19e0a restored by streaming, `lake build Checked` (3828 jobs with the new modules), `lake env lean` of an axiom print (propext, Classical.choice, Quot.sound), StatementDeps relock, `Claims.lean`, the trust checks, `records_check.py 0f19e0a`.
- CI read in this run: 45763705693 (0f19e0a) green on every job → `bonnor_ebert_turning_decay` judged PROVED.
- Message to Alexander (L.2): `bonnor_ebert_turning_decay` PROVED (judged by CI on every job).
