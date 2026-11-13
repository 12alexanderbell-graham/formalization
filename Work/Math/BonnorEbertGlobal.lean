import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Checked.Math.BonnorEbert

/-! Bonnor–Ebert sphere, `BonnorEbertGlobal` (FROZEN by run 2026-11-13T2228Z before proof).

Same setting and conventions as `Checked/Math/BonnorEbert.lean`: the isothermal (Emden–Chandrasekhar)
equation w'' + (2/s) w' + e^w = 0 for w = −ψ (ρ = ρ_c e^{−ψ}), w(0) = 0, φ = w' with one-sided derivatives on
[0, S] and φ continuous at 0; the pressure-confined mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π).

The audited headline `bonnor_ebert_critical` shows that m rises strictly up to a radius ξ₁ in a seven-decimal
window and falls strictly from ξ₁ to radius 7. This file states the global companion: on the whole interval
[0, S] (any S at least 7, so on every radius a solution reaches) the first maximum is the strict global maximum
of the mass: every other radius has a strictly smaller mass. Physically, no pressure-confined isothermal
sphere, of any radius, has a larger dimensionless mass than the critical Bonnor–Ebert sphere. -/

namespace Work.Math.BonnorEbertGlobal
open Set

/-- Bonnor–Ebert critical mass is the global maximum: for every S ≥ 7 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, there is a radius ξ₁ between 6.4507514 and 6.4507515 such that the dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π) at every other radius s in [0, S] is strictly smaller than at ξ₁, and the
mass at ξ₁ lies between 1.1822265 and 1.1822266. -/
theorem bonnor_ebert_global (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      1.1822265 ≤ ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 := by
  sorry

end Work.Math.BonnorEbertGlobal
