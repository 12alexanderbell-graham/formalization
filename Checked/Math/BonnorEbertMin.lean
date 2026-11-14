import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Checked.Math.BEHMain

/-! Bonnor–Ebert sphere, `BonnorEbertMin`: beyond the critical sphere the pressure-confined mass falls to a first minimum, and that minimum is the strict minimum of the mass over every radius from the critical one to the end of the solution. Promoted from `Work/Math/BonnorEbertMin.lean` (frozen and proved by run 2026-11-14T0428Z); the route is `BEHMain` (certified cells in homology variables, then Volterra's function). -/

namespace Checked.Math.BonnorEbertMin
open Set

/-- Bonnor–Ebert sphere, min of the mass: for every S ≥ 150 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are ξ₁ between 6.4507514 and 6.4507515 and ξ₂
between 67.0075 and 67.0076 such that m(s) < m(ξ₁) for s in [0, S] with s ≠ ξ₁, m(ξ₂) < m(s) for s in [ξ₁, S]
with s ≠ ξ₂, m(ξ₂) lies between 0.694366 and 0.694367, and the density contrast e^{−w(ξ₂)} lies between
2579.69 and 2579.71. -/
theorem bonnor_ebert_min (S : ℝ) (hS : 150 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.694366 ≤ ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.694367 ∧
      2579.69 ≤ Real.exp (-w ξ₂) ∧ Real.exp (-w ξ₂) ≤ 2579.71 :=
  Checked.Math.BEHMain.main S hS w φ hw hφ0 hφ h0

end Checked.Math.BonnorEbertMin
