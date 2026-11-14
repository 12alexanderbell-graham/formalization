import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Checked.Math.BEH2Main

/-! Bonnor–Ebert sphere, `BonnorEbertMax2`: beyond the first minimum the pressure-confined mass rises to a second maximum, and that maximum is the strict maximum of the mass over every radius from the first minimum to the end of the solution. Promoted from `Work/Math/BonnorEbertMax2.lean` (frozen and proved by run 2026-11-14T1028Z); the route is `BEH2Main` (certified cells in homology variables, then Volterra's function). -/

namespace Checked.Math.BonnorEbertMax2
open Set

/-- Bonnor–Ebert sphere, second max of the mass: for every S ≥ 2000 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are ξ₁ between 6.4507514 and 6.4507515, ξ₂
between 67.0075 and 67.0076 and ξ₃ between 733.5 and 734 such that m(s) < m(ξ₁) for s in [0, S] with
s ≠ ξ₁, m(ξ₂) < m(s) for s in [ξ₁, S] with s ≠ ξ₂, m(s) < m(ξ₃) for s in [ξ₂, S] with s ≠ ξ₃, m(ξ₃) lies
between 0.8306 and 0.8308, and the density contrast e^{−w(ξ₃)} lies between 258300 and 258800. -/
theorem bonnor_ebert_second_max (S : ℝ) (hS : 2000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ ξ₃ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₂ S, s ≠ ξ₃ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.8306 ≤ ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.8308 ∧
      258300 ≤ Real.exp (-w ξ₃) ∧ Real.exp (-w ξ₃) ≤ 258800 :=
  Checked.Math.BEH2Main.main S hS w φ hw hφ0 hφ h0

end Checked.Math.BonnorEbertMax2
