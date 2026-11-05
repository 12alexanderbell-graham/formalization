# Run 2026-11-05T0628Z (scheduled)

**THE RESULT:** part 2 (new science; idle four runs, taken by rotation) moved: the global minimum of a published cosmological fit statistic certified in Lean over the whole parameter region — the open-ΛCDM χ² of the thirty cosmic-chronometer H(z) points of Moresco et al. 2016 (Table 4, H₀ prior 73 ± 2.4) lies in [14.9665, 14.9675), i.e. 14.967 to three decimals — and with it the part-1 question left open by run 0428Z: the printed oΛCDM AICc 21.41 is below every value the paper's Eq. 5.4 can give.

**What can a scientist now trust without checking it themselves, that they could not before?** That no H₀ and no (Ω_m ≤ 1, Ω_Λ ≥ 0) with real expansion rate fit Moresco et al.'s Table 4 better than χ² = 14.9665 (with the H₀ prior term), and that a fit below 14.9675 exists inside the paper's prior region: the minimum is 14.967 to three decimals, proved over the whole region (not found by a minimiser), exact arithmetic, standard axioms. Consequence: with −2 ln L_max = χ², k = 3 and any N ≤ 31, AICc ≥ 21.855, so the printed 21.41 cannot come from Eq. 5.4 at any parameter values.

**Weakest unchecked step:** the transcription of Table 4 (PRINTED) is read twice (run 0428Z: blind transcription equal entry by entry, and this run's blind restater's own table, both by models from the PDF), but the second reading is a Work theorem, not yet a Checked second reading; and the reading of Table 5's column as AICc of Eq. 5.4 with −2 ln L = χ² including the prior (referee: plain AIC, or a data-only likelihood, would make 21.41 attainable).

**Kind of answer (PROMPT note 1228Z):** not in print — the with-prior minimum is not printed anywhere the referee found; the nearest is Wei, Melia & Wu 2017 (arXiv:1612.08491, Table 1), who fit the same points without the prior (χ² ≈ 14.46, reproduced by the referee from this table). No certified global minimum of a cosmological χ² was found in print. The JCAP version was not reachable.

## Start
- 06:28Z: no LOCK; LOCK + README stub 14541c1. add_repo not exposed; pre-cloned detached HEAD, stale local main reset to origin/main. Local Lean: elan installer accepted, Mathlib cache.
- CI of run 0428Z: 2a6f31c 41974363342, 80d439c 41974602988, 2f6000f 41975164683 green; b7669c9 41978378541 running at start.

## Work
1. **Region and feasibility** (`scripts/feas_wide.py`, `opt_float.py`): with Ω_m ≤ 1, Ω_Λ ≥ 0 and E²(1.965) ≥ 0 the region lies in [−1, 1] × [0, 4]; float bisection closes c = 14.9665 with ~600 boxes (even 14.967 with 737).
2. **Freeze** 1daa626 `Work/Data/Moresco16Min.lean`: `chiSqOL_ge`, `chiSqOL_lt`, `chiSqOL_glb_prior`, `chiSqOL_glb_wide` (IsGLB, no sInf junk), `table5_oL_aicc_unattainable`.
3. **In one message:** blind restater (Sonnet, from the PDF only: own table, (H₀, Ω_m, z_t), H₀ > 0, E² > 0, N ∈ 5..50) and referee (independent 50-digit branch and bound).
4. **Proof** (`Moresco16MinTools.lean`, `Moresco16MinCerts0–3.lean`, `Moresco16MinCover.lean`; `scripts/gen_min.py` exact-rational bisection, `emit_min.py`): H₀ profiled exactly (χ² quadratic in H₀, discriminant), √E² ≤ (E² + s²)/(2s), convexity → four corner checks per box; 905 leaves (662 closed by `decide +kernel` over ℚ through a cast bridge, 243 vacuous). First version with `norm_num` cost ≈ 20 s per box (≈ 3.7 h); kernel evaluation ≈ 1 s per box (all certificates ≈ 20 min on 2 cores). Statements and docstrings byte-identical to the freeze (script check). Commit 09b58c7.
5. **Audit:** blind restatement closed (`Moresco16MinBlindClosed.lean`, statements identical to the blind file; claim B for every N ≤ 50 follows from `chiSqOL_ge`). Referee STANDS-WITH-CORRECTIONS (`referee_min.md`): minimum 14.967038174884521725 at (Ω_m, Ω_Λ, H₀) = (0.43617, 0.98144, 72.2865), single basin, boundaries ≥ 28; corrections added to the module doc after the freeze (LEDGER).
6. **Probe** (branch `probe/kernel-decide`, b5f32d5, not merged): one box decided by `decide +kernel` in a Checked module, to learn whether nanoda and the trust step accept kernel evaluation before any promotion uses it.

## Next
Read CI of 09b58c7 (work job builds the cover, ≈ 20 min) and of the probe branch (checked job: nanoda on `decide +kernel`). Then promote Moresco16 + Moresco16Min to Checked (m16Table PRINTED with the second reading moved to `Checked/Trust/`, `e2OL`/`chiSqOL` FORMULA or pinned, register headlines, relock, CLAIMS.md, packet), or regenerate the certificates with `norm_num` if nanoda refuses the kernel evaluation.
