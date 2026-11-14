# Run 2026-11-14T1828Z (scheduled)

**THE RESULT:** parts 2/5 (rotation: part 3 moved at 1628Z, parts 2/5 and 1 at 1428Z) — the next turn of the Bonnor–Ebert mass curve is a machine-checked statement: for every regular solution of the isothermal equation, beyond the second minimum the pressure-confined mass rises to a third maximum at a radius in [84497, 84516] (mass in [0.80091, 0.800916], centre-to-edge density contrast in [3556300000, 3558000000]), and that maximum is strictly above the mass at every other radius from the second minimum on. Frozen before proof, proved in Work, blind restatement closed, referee STANDS, promoted to Checked (`Checked.Math.BonnorEbertMax3.bonnor_ebert_third_max`) with NV witness, literal readings and all five hypotheses classified. Kind (part 2): the referee found no value of this maximum in print and no rigorous enclosure of any Bonnor–Ebert extremum.

**What can a scientist now trust without checking it themselves, that they could not before?** That every pressure-confined isothermal sphere at least as centrally condensed as the second-minimum sphere has a dimensionless mass of at most 0.800916 (attained exactly once, at a radius between 84497 and 84516) — for every solution of the equation, not one floating-point trajectory.

**Weakest unchecked step:** the meaning of the windows rests on the blind restatement and the referee (both language models), as for the first four extrema; CI has not yet judged this run's promotion (main's checked job of fc559f2 was still running at the end).

## Start
- 18:28Z. add_repo not exposed; pre-cloned checkout detached with a stale, shallow local main; `git fetch --unshallow origin && git checkout -B main origin/main` = 0ed4bdf. No LOCK → taken (93ac910).
- Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43590961602 (071b543) downloaded (2.5 GB) and restored; disk allowance tight (1.8 GB free after the restore: deleted the zip and `~/.cache/mathlib`); `lake build Checked.Math.BEOMain` (the BEO modules of fc559f2) ≈ 4 min.
- CI at start: 43611102762 (fc559f2, `bonnor_ebert_second_min`) checked job running since 16:40Z, nanoda shards 0, 1, 3 green, shard 2 running; 43624324234 (0ed4bdf) pending.

## Bottleneck (and what a yes/no changes)
- STATE 0t by rotation, parts 2/5: the third maximum (ξ ≈ 84506) as a generator run of run 1428Z's one-sided cells plus a Volterra tail from above. Yes: the spiral's next turn is certified and the cells are shown to carry a further order of magnitude in radius with no new mathematics; no: record where the one-sided bound or the tail fails.

## What we did
1. **Float study** (`study/max3.py`, unchecked): ξ₅ ≈ 84506.33, m ≈ 0.8009120; the maximum of u v³ on the Volterra sublevel set falls below 4π m(ξ₅)² ≈ 8.0608 only from ≈ 2·10⁵ on (8.056 at 2·10⁵, 8.046 at 3·10⁵): tail at 300000.
2. **Generator** `scripts/gen_b3.py` (adapted from run 1428Z's `gen_bo.py`; start = the state at 20000 that `BEOChain` certifies, box 2·10⁻⁷): 79 cells on [20000, 300000], radius 8·10⁻⁷ → 3.2·10⁻⁷, μ ≈ −0.49 … −0.50 per unit log-radius. The bracket of ξ₅ must be ≥ ≈ 8 from the zero (the cell invariant's margin 3B on 2u − v against (2u − v)' ≈ 1.8·10⁻⁷ per unit radius): [84497, 84516] passes, [84504, 84509] fails 26 cells.
3. **Freeze** (64190b0) of `Work.Math.BonnorEbertMax3.bonnor_ebert_third_max` (statement of `bonnor_ebert_second_min` plus ξ₅, the strict maximum over [ξ₄, S], mass and contrast windows; S ≥ 300000), compiled with `sorry` first; briefs in the same commit; blind restater (Sonnet, 26 s) and referee (Opus, 9 min) launched in one message while the cells compiled.
4. **Proof** (3261828): `emit_b3.py` → `BE3Data.lean` (9 segments, kernel ≈ 50 s), `BE3Chain.lean` (one fix: a non-reduced rational literal needs `decide +kernel`, not `rfl`), `BE3Tail.lean` (u v³ < 8.05 on the sublevel set at 300000; first time), `BE3Main.lean` (calls the Checked second-minimum assembly for ξ₁ … ξ₄; re-derives the zero ζ of 2u − v in the second-minimum bracket and proves ξ₄ = ζ because both are strict minimisers on sets containing each other — so no copy of that assembly; IVT for ξ₅; monotonicity of u v³ on [ξ₄, ξ₅] and [ξ₅, 300000]; tail). Two `linarith` calls over `set` variables failed and were replaced by definitional facts. Axioms propext, Classical.choice, Quot.sound.
5. **Audit:** blind restatement (structure with `derivWithin ψ (Ici 0) 0 = 0` and the equation in `deriv` form) closed in `Work/Math/BonnorEbertMax3BlindClosed.lean` first time (adapted from the second-minimum closure: for ξ > 0, `deriv` of x²ψ' is the genuine derivative); referee STANDS (`referee/REPORT.md`).
6. **Promotion** (`scripts/promote_be_max3.py`): `Checked/Math/{BE3Data,BE3Chain,BE3Tail,BE3Main,BonnorEbertMax3}.lean`, headline docstring in the house style, NV witness (Gelfand existence at 300000), literal readings (those of the second minimum), `Checked/Trust/NecessityAG.lean` (1, 2, 4, 5 NEEDED, 3 REDUNDANT, adapted from NecessityAF; compiled first time).

## Results
- `bonnor_ebert_third_max`: PROVED in Work + AUDITED; promoted to Checked (local build green); PROVED once a main run is green on every job.

## Not done / next
- STATE 0u.

## Local checks and push
- See the final commit message (filled below at the end of the run).
