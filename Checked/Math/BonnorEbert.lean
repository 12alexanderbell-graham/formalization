import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Math.BEMain

/-! Bonnor–Ebert sphere, `BonnorEbert`: the critical state of the pressure-confined isothermal sphere: the first maximum of the dimensionless mass, its radius, mass and centre-to-edge density contrast, as printed in the statement of `bonnor_ebert_critical`. Promoted from `Work/Math/BonnorEbert.lean`. -/

namespace Checked.Math.BonnorEbert
open Set

/-- Bonnor–Ebert critical sphere: for every S ≥ 7 and every solution w of w'' + (2/s)w' + e^w = 0 on
(0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous at 0, there is a radius ξ₁
between 6.4507514 and 6.4507515 such that the dimensionless mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π)
increases strictly on [0, ξ₁] and decreases strictly on [ξ₁, 7]; there the mass lies between 1.1822265 and
1.1822266 and the centre-to-edge density contrast e^{−w(ξ₁)} between 14.042032 and 14.042033. -/
theorem bonnor_ebert_critical (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 ξ₁) ∧
      StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc ξ₁ 7) ∧
      1.1822265 ≤ ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 ∧
      14.042032 ≤ Real.exp (-w ξ₁) ∧ Real.exp (-w ξ₁) ≤ 14.042033 :=
  Checked.Math.BEMain.bonnor_ebert_critical S hS w φ hw hφ0 hφ h0

end Checked.Math.BonnorEbert
