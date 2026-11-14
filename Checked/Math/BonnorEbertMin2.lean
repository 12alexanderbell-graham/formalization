import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Checked.Math.BEH2Main
import Checked.Math.BEOMain

/-! Bonnor–Ebert sphere, `BonnorEbertMin2`: beyond the second maximum the pressure-confined mass falls to a second minimum, and that minimum is the strict minimum of the mass over every radius from the second maximum to the end of the solution. Promoted from `Work/Math/BonnorEbertMin2.lean` (frozen and proved by run 2026-11-14T1428Z); the route is `BEOMain` (one-sided cells in homology variables, then Volterra's function). -/

namespace Checked.Math.BonnorEbertMin2
open Set

/-- Bonnor–Ebert sphere, second min of the mass: for every S ≥ 20000 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are ξ₁ between 6.4507514 and 6.4507515, ξ₂
between 67.0075 and 67.0076, ξ₃ between 733.5 and 734 and ξ₄ between 7849.5 and 7849.75 such that
m(s) < m(ξ₁) for s in [0, S] with s ≠ ξ₁, m(ξ₂) < m(s) for s in [ξ₁, S] with s ≠ ξ₂, m(s) < m(ξ₃) for s in
[ξ₂, S] with s ≠ ξ₃, m(ξ₄) < m(s) for s in [ξ₃, S] with s ≠ ξ₄, m(ξ₄) lies between 0.787992 and 0.787995,
and the density contrast e^{−w(ξ₄)} lies between 31193900 and 31196100. -/
theorem bonnor_ebert_second_min (S : ℝ) (hS : 20000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧ 7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₂ S, s ≠ ξ₃ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₃ S, s ≠ ξ₄ →
        ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.787992 ≤ ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.787995 ∧
      31193900 ≤ Real.exp (-w ξ₄) ∧ Real.exp (-w ξ₄) ≤ 31196100 :=
  Checked.Math.BEOMain.main S hS w φ hw hφ0 hφ h0

end Checked.Math.BonnorEbertMin2
