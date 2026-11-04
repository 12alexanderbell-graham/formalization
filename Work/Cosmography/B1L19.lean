import Checked.Cosmography.B1Fit

/-!
# B1, fourth order: the quasar-driven Lusso et al. 2019 log-polynomial fits are not the image of any flat ΛCDM model over the quasar range

**Question (STATE "B1", "Not yet": the Lusso et al. 2019/2020 fourth-order fits).**
Lusso et al. 2019 (A&A 628, L4; arXiv:1907.07692v4, Eq. (7)) fit
`D_L = k ln(10)(c/H₀)(x + a₂x² + a₃x³ + a₄x⁴)`, `x = log₁₀(1+z)`, with a free normalisation `k`
per sample, to supernovae, quasars and gamma-ray bursts, and report the best fits in their Table 2
(SNe + quasars + GRBs: `a₂ = 3.205`, `a₃ = 3.564`, `a₄ = −2.510`; SNe + quasars: `3.075`, `4.466`,
`−3.716`; each with asymmetric 1σ ranges). They measure the tension with ΛCDM as the distance of
these coefficients from the Taylor values of their Eq. (8). The critique (Yang et al. 2020,
arXiv:1911.01681; Banerjee et al. 2021, arXiv:2009.04109) is that the truncated series represents
exact ΛCDM badly at high redshift, so coefficient distances from the Taylor point are not evidence
against ΛCDM.

This file compares the fitted *curves* with the *exact* flat ΛCDM distance, not with the Taylor
coefficients, so truncation cannot enter: the normalisation (`k`, `H₀`, any magnitude offset)
cancels in the difference of distance moduli between two redshifts of the same sample. The two
redshifts `1 + z = 2√2` and `1 + z = 4√2` (`z` between 1.8 and 4.7) lie inside the quasar range.

**Statements (frozen before proof).**
* `l19_sq_central`, `l19_sqg_central`: at the printed central coefficients, for every Ω ∈ [0, 1]
  and every scale factor obeying `H = H₀√(Ω(1+z)³ + 1 − Ω)` back to the farther source, the exact
  distance modulus rises between the two redshifts by more than the fitted quartic's does, by more
  than 7/20 mag (SNe + quasars) and 3/10 mag (SNe + quasars + GRBs).
* `l19_sq_box`, `l19_sqg_box`: the same with margin 0 for *every* quartic whose coefficients lie at
  or beyond the printed 1σ ends in the direction that brings the curve closer to ΛCDM
  (`a₂ ≥ 2.906`, `a₃ ≤ 5.479`, `a₄ ≤ −1.794` for SNe + quasars, the printed central value minus or
  plus one printed σ; `a₂ ≥ 3.043`, `a₃ ≤ 4.480`, `a₄ ≤ −0.915` for SNe + quasars + GRBs). This
  region contains the whole coordinate box of the printed ±1σ ranges; no covariance is printed, and
  the statement needs none.

Positivity of the polynomial distance at the farther redshift is assumed in the box statements (a
negative distance has no distance modulus; `Real.logb` would silently take the absolute value); at
the central values it is a consequence.

Floating-point exploration (`runs/2026-11-04T1228Z/scripts/`): the exact ΛCDM ratio
`d_L(4√2 − 1)/d_L(2√2 − 1)` decreases on a grid of Ω from 5.09 (Ω = 0) to 2.859 (Ω = 1); the central quartics
give 2.401 (SNe + quasars) and 2.470 (+ GRBs), the box corners 2.821 and 2.829; the SNe + GRBs fit
(no quasars; `a₂ = 3.304`, `a₃ = 2.069`, `a₄ = 2.571`) gives 3.044, matched by Ω ≈ 0.34. These floating-point numbers are not
claims of the theorems.

Conventions: as `Checked.Cosmography.B1` (`c = 1`, `hubble a t = ȧ/a`,
`redshift a t₀ t = a(t₀)/a(t) − 1`, `lumDistFlat`; distance-modulus difference `5 log₁₀(d/d')`).

FROZEN (annex 40.1) in run 2026-11-04T1228Z before proof work.
-/

namespace Work.Cosmography.B1L19

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- The fourth-order log-polynomial luminosity distance of Lusso et al. 2019, Eq. (7):
`D_L = ln(10) (c/H₀) (x + a₂x² + a₃x³ + a₄x⁴)`, `x = log₁₀(1+z)`, with `c = 1` and the free
normalisation `k` absorbed into `H₀`. -/
noncomputable def logPolyDL4 (a₂ a₃ a₄ H₀ z : ℝ) : ℝ :=
  Real.log 10 / H₀ *
    (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3
      + a₄ * Real.logb 10 (1 + z) ^ 4)

/-- **Lusso et al. 2019, SNe + quasars, central fit.** For every `Ω ∈ [0, 1]` and every scale factor
obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther source,
with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`, the quartic
log-polynomial distance with the printed central coefficients `a₂ = 3.075`, `a₃ = 4.466`,
`a₄ = −3.716` (Table 2) has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact luminosity
distance `d_L` (`lumDistFlat`) that is larger at the farther source: the residual at
`1 + z = 4√2` exceeds the one at `1 + z = 2√2` by more than 7/20 mag. No normalisation and no
magnitude offset can remove this difference. -/
theorem l19_sq_central (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    7 / 20 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₃)) := by
  sorry

/-- **Lusso et al. 2019, SNe + quasars + GRBs, central fit.** For every `Ω ∈ [0, 1]` and every scale
factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther
source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`, the
quartic log-polynomial distance with the printed central coefficients `a₂ = 3.205`, `a₃ = 3.564`,
`a₄ = −2.510` (Table 2) has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact luminosity
distance `d_L` (`lumDistFlat`) that is larger at the farther source: the residual at
`1 + z = 4√2` exceeds the one at `1 + z = 2√2` by more than 3/10 mag. No normalisation and no
magnitude offset can remove this difference. -/
theorem l19_sqg_central (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    3 / 10 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₃)) := by
  sorry

/-- **Lusso et al. 2019, SNe + quasars, the whole 1σ range.** For every `Ω ∈ [0, 1]` and every scale
factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther
source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, every quartic log-polynomial distance with
`a₂ ≥ 2.906`, `a₃ ≤ 5.479`, `a₄ ≤ −1.794` (the printed Table 2 ends of the 1σ ranges on the side
that brings the quartic's distance ratio closer to the exact one; the region contains the box of all three printed ±1σ ranges), normalisation `H > 0`
and positive at the farther source has a residual distance modulus `5 log₁₀(d_L / D_L)` against
the exact luminosity distance `d_L` (`lumDistFlat`) that is strictly larger at `1 + z = 4√2` than at
`1 + z = 2√2`. -/
theorem l19_sq_box (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H)
    (ha₂ : 2.906 ≤ a₂) (ha₃ : a₃ ≤ 5.479) (ha₄ : a₄ ≤ -1.794)
    (hp₅ : 0 < logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) :
    5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃))
      < 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) := by
  sorry

/-- **Lusso et al. 2019, SNe + quasars + GRBs, the whole 1σ range.** For every `Ω ∈ [0, 1]` and
every scale factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to
the farther source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, every quartic log-polynomial
distance with `a₂ ≥ 3.043`, `a₃ ≤ 4.480`, `a₄ ≤ −0.915` (the printed Table 2 ends of the 1σ ranges
on the side that brings the quartic's distance ratio closer to the exact one; the region contains the box of all three printed ±1σ ranges),
normalisation `H > 0` and positive at the farther source has a residual distance modulus
`5 log₁₀(d_L / D_L)` against the exact luminosity distance `d_L` (`lumDistFlat`) that is strictly
larger at `1 + z = 4√2` than at `1 + z = 2√2`. -/
theorem l19_sqg_box (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H)
    (ha₂ : 3.043 ≤ a₂) (ha₃ : a₃ ≤ 4.480) (ha₄ : a₄ ≤ -0.915)
    (hp₅ : 0 < logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) :
    5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃))
      < 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) := by
  sorry

end Work.Cosmography.B1L19
