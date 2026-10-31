import Mathlib
import Checked.Cosmography.BambaDLy

/-!
# Blind restatement B1: flat ΛCDM luminosity distance vs. the Risaliti–Lusso log-polynomial

Conventions (from `Checked.Cosmography`): `hubble a t = ȧ(t)/a(t)`,
`redshift a t₀ t = a(t₀)/a(t) − 1`,
`BambaY.lumDistFlat a t₀ t = a(t₀) (1 + z) ∫_t^{t₀} ds / a(s)` (`c = 1`).
-/

namespace Work.Cosmography.B1Blind

open Checked.Cosmography Checked.Cosmography.BambaY

/-- (C0) The scale factor `a` is a spatially flat ΛCDM model with present matter fraction `Ω` on
the whole past interval `[t, t₀]` from emission `t` to observation `t₀`:
`a` is positive and (two-sidedly) differentiable at every point of `[t, t₀]`, `H₀ = H(t₀) > 0`,
and `H(s) = H₀ √(Ω (1 + z(s))³ + 1 − Ω)` for every `s ∈ [t, t₀]`. -/
structure FlatLCDMOn (a : ℝ → ℝ) (Ω t t₀ : ℝ) : Prop where
  le : t ≤ t₀
  pos : ∀ s ∈ Set.Icc t t₀, 0 < a s
  diff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s
  H0_pos : 0 < hubble a t₀
  friedmann : ∀ s ∈ Set.Icc t t₀,
    hubble a s = hubble a t₀ * Real.sqrt (Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)

/-- (C1) In such a model, with `0 ≤ Ω ≤ 1`,
`d_L = (1 + z)/H₀ · ∫_{w}^{1} 2/√(Ω + (1 − Ω) v⁶) dv` with `w = √(a(t)/a(t₀))`. -/
theorem lumDist_eq_integral (a : ℝ → ℝ) (Ω t t₀ : ℝ) (hΩ0 : 0 ≤ Ω) (hΩ1 : Ω ≤ 1)
    (hM : FlatLCDMOn a Ω t t₀) :
    lumDistFlat a t₀ t =
      (1 + redshift a t₀ t) / hubble a t₀ *
        ∫ v in Real.sqrt (a t / a t₀)..1, 2 / Real.sqrt (Ω + (1 - Ω) * v ^ 6) := by
  sorry

/-- `x = log₁₀(1 + z)`. -/
noncomputable def logx (z : ℝ) : ℝ := Real.logb 10 (1 + z)

/-- Flat-ΛCDM value of the coefficient `a₂ = ln 10 · (3/2 − (3/4) Ω)`. -/
noncomputable def coeffA2 (Ω : ℝ) : ℝ := Real.log 10 * (3 / 2 - 3 / 4 * Ω)

/-- Flat-ΛCDM value of the coefficient `a₃ = ln² 10 · ((9/8) Ω² − 2 Ω + 7/6)`. -/
noncomputable def coeffA3 (Ω : ℝ) : ℝ := Real.log 10 ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)

/-- The third-order log-polynomial of Risaliti & Lusso 2019 (`c = 1`):
`D_L = ln(10) (1/H₀) (x + a₂ x² + a₃ x³)`, `x = log₁₀(1 + z)`. -/
noncomputable def logPoly (H₀ a₂ a₃ z : ℝ) : ℝ :=
  Real.log 10 * (1 / H₀) * (logx z + a₂ * logx z ^ 2 + a₃ * logx z ^ 3)

/-- The log-polynomial with the flat-ΛCDM coefficients for matter fraction `Ω`. -/
noncomputable def logPolyLCDM (H₀ Ω z : ℝ) : ℝ := logPoly H₀ (coeffA2 Ω) (coeffA3 Ω) z

/-- Distance-modulus difference `Δμ = 5 log₁₀(d_L^exact / D_L^poly)` for a source emitting at `t`,
the polynomial using the model's own `H₀` and `Ω`. -/
noncomputable def deltaMu (a : ℝ → ℝ) (Ω t₀ t : ℝ) : ℝ :=
  5 * Real.logb 10
    (lumDistFlat a t₀ t / logPolyLCDM (hubble a t₀) Ω (redshift a t₀ t))

/-- (C2) For every `Ω ∈ [0.2, 0.4]` and every such model, at a source with `z = 3`, the
log-polynomial is positive and `Δμ > 0.09`. -/
theorem claim_z3 (a : ℝ → ℝ) (Ω t t₀ : ℝ) (hΩ : Ω ∈ Set.Icc (0.2 : ℝ) 0.4)
    (hM : FlatLCDMOn a Ω t t₀) (hz : redshift a t₀ t = 3) :
    0 < logPolyLCDM (hubble a t₀) Ω (redshift a t₀ t) ∧ 0.09 < deltaMu a Ω t₀ t := by
  sorry

/-- (C3) Same as (C2) at `z = 7`, with `0.3` in place of `0.09`. -/
theorem claim_z7 (a : ℝ → ℝ) (Ω t t₀ : ℝ) (hΩ : Ω ∈ Set.Icc (0.2 : ℝ) 0.4)
    (hM : FlatLCDMOn a Ω t t₀) (hz : redshift a t₀ t = 7) :
    0 < logPolyLCDM (hubble a t₀) Ω (redshift a t₀ t) ∧ 0.3 < deltaMu a Ω t₀ t := by
  sorry

/-- (C4) In one such model (same `a`, `t₀`, `Ω ∈ [0.2, 0.4]`) with sources at `z = 3` (emitted at
`t₃`) and `z = 7` (emitted at `t₇`), `Δμ(z = 7) − Δμ(z = 3) > 0.18`. -/
theorem claim_diff (a : ℝ → ℝ) (Ω t₃ t₇ t₀ : ℝ) (hΩ : Ω ∈ Set.Icc (0.2 : ℝ) 0.4)
    (hM₃ : FlatLCDMOn a Ω t₃ t₀) (hM₇ : FlatLCDMOn a Ω t₇ t₀)
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7) :
    0.18 < deltaMu a Ω t₀ t₇ - deltaMu a Ω t₀ t₃ := by
  sorry

end Work.Cosmography.B1Blind
