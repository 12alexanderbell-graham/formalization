# Run 2026-11-14T1428Z (scheduled)

**THE RESULT:** parts 2/5 and 1 (rotation: part 3 moved at 1228Z, parts 2/5 at 1028Z, part 1 at 0828Z; the new cell type is simulator infrastructure, part 1, and its first use is a new certified extremum, parts 2/5) — the validated simulator no longer loses accuracy along the Bonnor–Ebert spiral, and the next turn of the mass curve is a machine-checked statement: for every regular solution of the isothermal equation, beyond the second maximum the pressure-confined mass falls to a second minimum at a radius in [7849.5, 7849.75] (mass in [0.787992, 0.787995], centre-to-edge density contrast in [31193900, 31196100]), and that minimum is strictly below the mass at every other radius from the second maximum on. Frozen before proof, proved in Work, blind restatement closed, referee STANDS, promoted to Checked (`Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min`) with NV witness, literal readings and all five hypotheses classified. Kind (part 2): the referee found no value of this minimum in print and no rigorous enclosure of any Bonnor–Ebert extremum.

**What can a scientist now trust without checking it themselves, that they could not before?** That every pressure-confined isothermal sphere at least as centrally condensed as the second-maximum sphere has a dimensionless mass of at least 0.787992 (attained exactly once, at a radius between 7849.5 and 7849.75) — for every solution of the equation, not one floating-point trajectory; and that a validated ODE enclosure of this spiral can contract instead of grow (one-sided cells: radius 8·10⁻⁷ at 150 → 1·10⁻⁷ at 20000, against ×340 growth of the Lipschitz cells from 150 to 2000).

**Weakest unchecked step:** the meaning of the windows rests on the blind restatement and the referee (both language models), as for the first three extrema; CI has not yet judged this run's promotion (main's checked job of 071b543 was still running at the end).

## Start
- 14:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main; `git fetch --unshallow origin && git checkout -B main origin/main` = fde8092. No LOCK → taken (c6ffa22).
- Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43581569718 (c3ca8a4) restored; `lake build Checked` to HEAD ≈ 10 min (BEH2* modules of 071b543).
- CI at start: 43590961602 (071b543) checked job running since 13:26Z; 43603610196 (fde8092) pending (later cancelled by this run's push b83fb8a, which contains it).

## Bottleneck (and what a yes/no changes)
- STATE 0q / LEDGER experiment of run 1028Z: one-sided cells in a weighted norm for the Bonnor–Ebert spiral. Yes: the enclosure stops growing, the second minimum (ξ ≈ 7850) and later turns become reachable by generator runs; no: record what the one-sided bound cannot see.

## What we did
1. **One-sided cells** `Work/Math/BEOCell.lean` (≈ 700 lines, written and compiled in ≈ 15 min): generic step `os_cell` (time-dependent field, weighted norm N(e) = 7e₁² + (e₁ + 2e₂)² from the real Jordan basis of the focus (1, 2), contracting bound μ ≤ 0; adapted from `Checked.Sim.OneSidedNeg`); the homology field's one-sided bound from four corner PSD checks (`qf`, `CornerOK`, `box_qf`, `os_box`: the field is quadratic, so F(y) − F(g) = J((y+g)/2)(y − g) and the form is affine in the midpoint); `CellProp` (box, corners, weighted defect, exp(μh) ≤ 1/(1 − μh)), invariants 1–4 (4 = (2u − v)' < 0 added), Minkowski links, `chainTo`, `seg_q`, `end_q`, `start_box`.
2. **Generator** `scripts/gen_bo.py` (exact rationals, mirrors `CellProp`): 153 cells of degree 12 on [150, 20000] from `BEHChain`'s state at 150, μ per cell by bisection on the corner test (−0.37 … −0.49 per unit log-radius), grid refined towards the two brackets [733.76, 733.78] and [7849.5, 7849.75]; enclosure 8·10⁻⁷ → 1.0·10⁻⁷. Float study `study/min2.py`.
3. **Freeze** (b0acc34) of `Work.Math.BonnorEbertMin2.bonnor_ebert_second_min` (statement of `bonnor_ebert_second_max` plus ξ₄ ∈ [7849.5, 7849.75], m(ξ₄) < m(s) for s ∈ [ξ₃, S] with s ≠ ξ₄, mass and contrast windows; S ≥ 20000), briefs in the same commit; blind restater (Sonnet, 29 s), referee (Opus, 4 min) and a fork for the tail lemma launched in one message.
4. **Proof** (b83fb8a): `emit_bo.py` → `BEOData.lean` (19 segments, kernel ≈ 75 s), `BEOChain.lean` (signs, bracket box and u window, state at 20000; 10 s), `BEOTail.lean` (fork: `dual'` with slopes −1/250, −3/500; u v³ > 7.805 beyond 20000), `BEOMain.lean` (calls `BEH2Main.main` for the first three extrema; no identification of ξ₃ needed: on [ξ₃, 733.76] u v³ ≥ its value at ξ₃ > 8.65, on the second-maximum bracket u v³ ≥ 1.02·2.04³, then monotone down to ξ₄, up to 20000, tail). Compiled after one `linarith` fix. Axioms propext, Classical.choice, Quot.sound.
5. **Audit:** blind restatement (C² on [0, ∞), two-sided `deriv` in mass and equation) closed in `Work/Math/BonnorEbertMin2BlindClosed.lean` first time (`deriv ψ 0 = 0` whether or not ψ is differentiable at 0); referee STANDS (`referee/REPORT.md`; second minimum ξ₄ = 7849.6320485, m = 0.7879941879, contrast 31195047.48; Volterra margin 0.0189 at 20000; no prior value in print found).
6. **Promotion** (`scripts/promote_be_min2.py`): `Checked/Math/{BEOCell,BEOData,BEOChain,BEOTail,BEOMain,BonnorEbertMin2}.lean`, headline docstring in the house style ("second min of the mass"), NV witness (Gelfand existence at 20000), literal readings (those of the maximum), `Checked/Trust/NecessityAF.lean` (1, 2, 4, 5 NEEDED, 3 REDUNDANT, adapted from NecessityAE).

## Results
- LEDGER experiment of run 1028Z ("one-sided cells in a weighted norm"): **confirmed** (LEDGER).
- `bonnor_ebert_second_min`: PROVED in Work + AUDITED; promoted to Checked (local build green); PROVED once a main run is green on every job.

## Not done / next
- STATE 0s.

## Local checks and push
- `lake build Checked` green (incremental on the restored build; BEOData ≈ 76 s, BEOChain 12 s); `#print axioms` of `Work.Math.BonnorEbertMin2.bonnor_ebert_second_min` and of the blind closure: propext, Classical.choice, Quot.sound.
- `TRUST_RELOCK=1 lake env lean scripts/trust/StatementDeps.lean` exit 0 (289 headlines; NV 172/172; necessity: needed 600 → 604, redundant 156 → 157, open 221 unchanged — the new headline enters fully classified); `Claims.lean` regenerated CLAIMS.md (289 claims); `make_packet.py` redrew the validation packet's sample (the new headline joins a stratum; mechanical, seed unchanged).
- `records_check.py c3ca8a4` (newest green ancestor): 41 commands, 0 failed.
- Final push removes the LOCK; its CI run judges the promotion (it replaces b83fb8a's pending run, whose content it contains).
