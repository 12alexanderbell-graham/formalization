import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Checked.Cosmography.BambaDLy

/-!
# B1: the third-order log-polynomial against exact flat ΛCDM (Risaliti & Lusso 2019)

**Question (TARGETS.md, B1).** Risaliti & Lusso 2019 (Nat. Astron. 3, 272; arXiv:1811.02590)
fit the quasar Hubble diagram with the third-order log-polynomial
`D_L = ln(10) (c/H₀) (x + a₂x² + a₃x³)`, `x = log₁₀(1+z)` (Methods, p. 15,
`runs/2026-10-30T1628Z/screen/RL19_p15_methods_a2_a3.png`), and measure a > 4σ tension as the
distance of the fitted `(a₂, a₃)` from the point that flat ΛCDM implies,
`a₂ = ln(10)(3/2 − 3/4 Ω_M)`, `a₃ = ln²(10)(9/8 Ω_M² − 2Ω_M + 7/6)` (Lusso et al. 2019,
A&A 628, L4, arXiv:1907.07692, Eq. (8), `.../L19_p3_eq8_a2_a3.png`; RL19's own text omits
the ln 10 powers but its Fig. 3 uses these values, screen 1628Z row 1). Lusso et al. 2019 say
the third-order expansion "is shown to reproduce a flat ΛCDM model up to z > 5, with only a
few per cent difference at the upper end of the redshift range".

**What is proved here, for every flat ΛCDM model with Ω_M ∈ [0.2, 0.4]** (any scale factor
solving `H = H₀ √(Ω(1+z)³ + 1 − Ω)` on the whole past interval back to the source):
1. `lumDistFlat_flatLCDM`: `d_L = (1+z)/H₀ · ∫_{w}^{1} 2 dv / √(Ω + (1−Ω)v⁶)`,
   `w = √(a(t)/a(t₀)) = (1+z)^{-1/2}` (the comoving integral in the variable `v = (1+z')^{-1/2}`).
2. `cubic_misses_z3`, `cubic_misses_z7`: the log-polynomial evaluated *at the ΛCDM-implied
   coefficients* differs from the exact ΛCDM distance modulus by more than 0.09 mag at z = 3
   and more than 0.3 mag at z = 7 (same H₀ on both sides).
3. `cubic_shape_miss`: the difference between the two misses (z = 7 minus z = 3) exceeds
   0.18 mag. This part does not depend on H₀ or on any magnitude zero point: a fit with a free
   normalisation cannot absorb it.

Conventions (as `Checked.Cosmography`): `c = 1`; `hubble a t = ȧ/a`;
`redshift a t₀ t = a(t₀)/a(t) − 1`; `lumDistFlat a t₀ t = a(t₀)(1+z)∫_t^{t₀} dt'/a(t')`;
distance-modulus difference of two distances `d, d'` is `5 log₁₀(d/d')`.
Flat ΛCDM on the interval `[t, t₀]`: `a > 0`, differentiable, `H₀ > 0`, and the Friedmann
law `H(s) = H₀ √(Ω(1+z(s))³ + 1 − Ω)` at every `s ∈ [t, t₀]` (not only near `t₀`, unlike
`Aviles.IsFlatLCDM`, which is local).

FROZEN (annex 40.1) in run 2026-10-31T0428Z before proof work.
-/

namespace Work.Cosmography.B1

open Checked.Cosmography Checked.Cosmography.BambaY

/-- ΛCDM-implied `a₂` of the log-polynomial, as printed in Lusso et al. 2019 Eq. (8). -/
noncomputable def lusA2 (Ω : ℝ) : ℝ := Real.log 10 * (3 / 2 - 3 / 4 * Ω)

/-- ΛCDM-implied `a₃` of the log-polynomial, as printed in Lusso et al. 2019 Eq. (8). -/
noncomputable def lusA3 (Ω : ℝ) : ℝ := Real.log 10 ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)

/-- The third-order log-polynomial luminosity distance of Risaliti & Lusso 2019 (Methods):
`D_L = ln(10) (c/H₀) (x + a₂x² + a₃x³)`, `x = log₁₀(1+z)`, with `c = 1`. -/
noncomputable def logPolyDL3 (a₂ a₃ H₀ z : ℝ) : ℝ :=
  Real.log 10 / H₀ *
    (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)

/-- **Bridge.** In a flat ΛCDM model on `[t, t₀]` the luminosity distance is
`(1+z)/H₀ · ∫_{√(a(t)/a(t₀))}^{1} 2/√(Ω + (1−Ω)v⁶) dv`. -/
theorem lumDistFlat_flatLCDM (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    lumDistFlat a t₀ t = (1 + redshift a t₀ t) / hubble a t₀ *
      ∫ v in √(a t / a t₀)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  sorry

/-- **B1, z = 3.** For every flat ΛCDM model with `Ω ∈ [0.2, 0.4]`, the third-order
log-polynomial at the ΛCDM-implied coefficients (same `H₀`) is positive at `z = 3` and
underestimates the exact distance modulus there by more than 0.09 mag. -/
theorem cubic_misses_z3 (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz : redshift a t₀ t = 3) :
    0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
    9 / 100 < 5 * Real.logb 10
      (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) := by
  sorry

/-- **B1, z = 7.** As `cubic_misses_z3`, at `z = 7`: more than 0.3 mag. -/
theorem cubic_misses_z7 (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz : redshift a t₀ t = 7) :
    0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
    3 / 10 < 5 * Real.logb 10
      (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) := by
  sorry

/-- **B1, shape (normalisation-free).** In every flat ΛCDM model with `Ω ∈ [0.2, 0.4]`, with
sources at `z = 3` (time `t₃`) and `z = 7` (time `t₇`), the miss of the ΛCDM-implied cubic
log-polynomial at `z = 7` exceeds its miss at `z = 3` by more than 0.18 mag. A change of `H₀`
(or of any magnitude zero point) in the polynomial shifts both misses equally. -/
theorem cubic_shape_miss (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7) :
    18 / 100 < 5 * Real.logb 10
        (lumDistFlat a t₀ t₇ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₇))
      - 5 * Real.logb 10
        (lumDistFlat a t₀ t₃ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₃)) := by
  sorry

end Work.Cosmography.B1
