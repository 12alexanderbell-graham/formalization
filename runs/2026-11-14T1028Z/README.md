# Run 2026-11-14T1028Z (scheduled)

**THE RESULT:** parts 2/5 by rotation (part 1 moved at 0828Z, part 3 at 0628Z, parts 2/5 last at 0428Z) — the next turn of the Bonnor–Ebert mass curve is now a machine-checked statement: for every regular solution of the isothermal equation, beyond the first minimum the pressure-confined mass rises to a second maximum at a radius in [733.5, 734] (mass in [0.8306, 0.8308], centre-to-edge density contrast in [258300, 258800]), and that maximum is strictly above the mass at every other radius from the first minimum onward. Frozen before proof, proved in Work, blind restatement closed, referee STANDS, promoted to Checked (`Checked.Math.BonnorEbertMax2.bonnor_ebert_second_max`) with NV witness, literal readings and all five hypotheses classified. Kind (part 2): the referee found no value of this maximum in print (older turning-point tables not read) and no proof that it is the largest mass beyond the first minimum; new are the certified numbers and the statement.

**What can a scientist now trust without checking it themselves, that they could not before?** That every pressure-confined isothermal sphere at least as centrally condensed as the first-minimum sphere has a dimensionless mass between 0.694366 and 0.8308, the upper end attained exactly once at a radius between 733.5 and 734 (density contrast enclosed) — for every solution of the equation, not one floating-point trajectory.

**Weakest unchecked step:** the meaning of the windows rests on the blind restatement and the referee (both language models), as for the first two extrema; CI has not judged this run's push (the checked jobs of 4a73412 and cb49239 were running for the whole run).

## Start
- 10:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main; `git fetch --unshallow origin && git checkout -B main origin/main` = 48e6826. No LOCK → taken (8d4bff0).
- Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43563791919 (96643b0) streamed and restored in ≈ 2 min; `lake build Checked` to HEAD ≈ 4 min.
- CI at start: 43579906667 (4a73412) and 43572789731 (cb49239) in progress, 43581569718 (c3ca8a4) pending.

## Bottleneck (and what a yes/no changes)
- STATE 0n (parts 2/5): the second maximum of the Bonnor–Ebert mass with the homology cells. Float study: ξ₃ ≈ 733.769, m ≈ 0.830690; the maximum of u v³ on the Volterra sublevel set at 2000 is 8.587 against 4π m(ξ₃)² = 8.671, so cells on [150, 2000] plus a Volterra bound from above settle "the second maximum is the largest mass beyond the first minimum". Yes: a third certified extremum and the mass range beyond ξ₂; no: record what limits the enclosure.

## What we did
1. **Freeze** (46adaf0) of `Work.Math.BonnorEbertMax2.bonnor_ebert_second_max` (hypotheses of `bonnor_ebert_min`; S ≥ 2000; windows from the generator's enclosures); briefs committed in the same commit; blind restater (Sonnet, 27 s) and referee (Opus, 4 min) launched in one message.
2. **Certificates** (`scripts/gen_bh2.py`, from run 0428Z's `gen_bh.py`): start = `BEHChain`'s state at 150 (radius 2·10⁻⁷); 83 cells with 2u − v > 0 to 733.55, bracket cell [733.55, 733.99] with 6u − 2u² − 3uv + v < 0, 47 cells with 2u − v < 0 to 2000; enclosure 7.4·10⁻⁶ at the bracket, 6.7·10⁻⁵ at 2000. First try failed on two cells (a long last cell before the bracket, a long first cell after it): refined grid near the bracket. `emit_bh2.py` → `BEH2Data.lean` (kernel 77–86 s), `emit_chain2.py` → `BEH2Chain.lean` (with `neg_G`, the opposite-sign bracket invariant proved beside the cell).
3. **Tail** `BEH2Tail.lean`: `dual'` with slopes 1/80 (u) and 3/160 (v/2) gives log(u v³/8) ≤ 80(V − 3) − … < log(865/800); the end enclosure is reduced to one corner by monotonicity of x − log x on (0, 1] and x − 2 log(x/2) on [2, ∞) (`f_anti`, `g_mono`; a plain interval bound lost 2.8·10⁻⁴ of the 4.6·10⁻⁴ budget). Compiled on the second attempt (`set` hid literals from `linarith`).
4. **Assembly** `BEH2Main.lean` (`make_main2.py`: `BEHMain.main` copied, statement and S ≥ 2000 changed, the new block appended): second chain, IVT for ξ₃ (`intermediate_value_Icc'`), uniqueness by (2u − v)' < 0, u v³ increasing on [ξ₂, ξ₃] (signs from `BEHChain`, the new chain and the bracket), decreasing on [ξ₃, 2000], below 8.65 beyond. The first build ran > 8 CPU-min: `nlinarith` inside the big context; moved to standalone lemmas `win_M`, `win_C`, `P_gt` → module 2 min. Proof d68e6e6, statement byte-identical; axioms propext, Classical.choice, Quot.sound.
5. **Audit:** blind restatement (derivative within [0, ∞) in mass and equation, ψ'(0) = 0 hypothesis) closed in `Work/Math/BonnorEbertMax2BlindClosed.lean` (S = 2000 and S = max ξ 2000; the three extremisers agree; ψ'(0) = 0 not even needed); referee STANDS (`referee/REPORT.md`).
6. **Promotion** (`scripts/promote_be2.py`): `Checked/Math/{BEH2Data,BEH2Chain,BEH2Tail,BEH2Main,BonnorEbertMax2}.lean` (module docs without numerals), headline docstring in the style of `bonnor_ebert_min` ("second max of the mass"; `second` added to `prose_vocab.txt`, LEDGER), NV witness (Gelfand existence at 2000), literal readings (those of the minimum), `Checked/Trust/NecessityAE.lean` (1, 2, 4, 5 NEEDED, 3 REDUNDANT).

## Not done / next
- STATE 0q. The second minimum (ξ ≈ 7849.6) by the same generator needs a tighter start (the ξ₃ windows are already limited to ≈ 4 digits by the enclosure inherited from radius 7).

## Local checks and push
