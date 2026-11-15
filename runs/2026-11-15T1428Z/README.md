# Run 2026-11-15T1428Z (scheduled)

**THE RESULT:** part 1 by rotation (trust track T2b, hypothesis necessity) — 48 hypotheses of the fourteen B1 headlines (log-polynomial distance fits tested against flat ΛCDM) classified in one module, `Checked/Trust/NecessityAP.lean`, with no new certificate: the time-order hypotheses NEEDED (27), the positivity of the scale factor REDUNDANT (14), and in the separation and published-fit box theorems the positivity of the normalisation and of the log-polynomial REDUNDANT (7).

**What can a scientist now trust without checking it themselves, that they could not before?** That none of the fourteen B1 claims silently depends on the scale factor being positive (the expansion law and differentiability already force one sign, and the sign does not matter), and that each stated ordering of the source times is load-bearing — without it the assumptions on the scale factor say nothing about the times where a distance is computed, and Lean exhibits a scale factor for which the claim fails. Measure: necessity NEEDED 639 → 666, REDUNDANT 164 → 185, open 196 → 148 (999 hypotheses, 172 headlines).

**Weakest unchecked step:** the 27 NEEDED witnesses are junk-value witnesses (Lean's integral of a non-integrable reciprocal is zero, and log 0 = 0): they show each statement is false in Lean without the hypothesis, not that a physical model violates it. The density-parameter bounds and the fit-residual hypotheses of the B1 family (the rest of its open list) still need certified integrals at other parameter values. CI has not judged this push; 43721065108 (b7d5a44, the `gelfand_extrema` promotion) was still running.

## Start
- 14:28Z. add_repo not exposed; pre-cloned checkout detached at b7d5a44 (= origin/main); `git fetch --unshallow origin && git checkout -B main origin/main`. No LOCK → taken (5ce855d).
- Local Lean: elan (authorized), `lake exe cache get`; `checked-build` of 43709741164 (0a52be0) downloaded to the scratchpad (≈ 2 min) and restored with `DELETE_ZIP=1` (disk then 3.8 GB free: deleted `~/.cache/mathlib`); `lake build Checked` to b7d5a44 ≈ 6 min.
- CI at start: 43709741164 (0a52be0) **success on every job** → `Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone` PROVED. 43721065108 (b7d5a44, the `gelfand_extrema` promotion) in progress (checked job in its Lean step from 14:14Z, nanoda shards running).

## Bottleneck (and what a yes/no changes)
- Rotation: part 1. STATE 1d named the LEDGER experiment of run 0628Z (selection hypotheses of `fs_neg_decay_max_shear` 13/16, `fs_neg_tenth_monotone_lt` 4/7, `fs_separation_equal` 8/17). A float study and a read of the existing stacks showed each needs a chain or lemma the stacks do not have (overshoot-then-return to p → 1; a suction start for the attached stack); the evaluation note is in LEDGER. The largest open block was the B1 family (14 headlines, ≈ 110 open hypotheses). Question: are its time-order and positivity hypotheses decidable without certified integrals? Yes → 48 hypotheses in one run.

## What we did
1. `sign_of_law`: a zero of the scale factor makes the Hubble rate zero (division by zero), while the flat law's right-hand side is H₀√(1 − Ω) > 0 for Ω < 1; IVT then gives one sign; `a ↦ -a` leaves hubble, redshift, `lumDistFlat`, `lumDist` and `omega0` unchanged. Redundancy of positivity in the five Ω ≤ 2/5 headlines.
2. `no_zero_core` (scratch `runs/2026-11-15T1428Z/lean/NoZero.lean`, compiled first time): at density one (Einstein–de Sitter, also the only zero-admitting case of the curved law since Ω ≤ 1 ≤ Ω₀) the law gives deriv a · √a = H₀√(a₀³) where a > 0; just after the last zero, MVT plus the derivative estimate at the zero give c² ≤ M³y for every small y: contradiction. Redundancy of positivity in the nine headlines whose density range reaches one.
3. Time order: `jb s = 16 (s² − 1/4)² (1 + s)²` (value one, Hubble rate two at time zero), source values written in by `Function.update` (`wa`); with the order reversed the law's interval is empty, and the reciprocal is not integrable across ±1/2 (`not_intervalIntegrable_of_sub_inv_isBigO_punctured`), so every luminosity distance is Lean's zero and each conclusion fails (log 0 = 0; the logPoly positivity hypotheses hold with positive coefficients). 27 witnesses.
4. Batch 2 (scratch `runs/2026-11-15T1428Z/lean/Batch2.lean`): within distance five quarters of the ΛCDM coefficients (density at most two fifths) the cubic log-polynomial is positive at one plus redshift up to ten, and with positive coefficients everywhere: the normalisation's positivity and the log-polynomial positivity hypotheses of `cubic_separation` (11, 12, 13) and `rl19_box_unmatched` (17–20) are REDUNDANT, each alone.
5. StatementDeps relock (new doc/moduledoc entries only), Claims (293, unchanged), packet, open baseline regenerated; `local_frozen_step.py --trust 0a52be0`; `records_check.py`.

## Next
- STATE 1e.
