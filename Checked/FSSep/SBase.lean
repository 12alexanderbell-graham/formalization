import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IntermediateValue
import Checked.FSNeg.NBase

/-! Falkner–Skan separation, the clamped field of the scaled adverse-sign problem with a free coefficient, the overshoot and slow-approach events from a zero wall value, and the certified chain shape. Module `SBase`, promoted from `Work/FSSep/SBase.lean`. -/

namespace Checked.FSSep.SBase
open Set Checked.FSNeg.NBase

/-- The clamped coefficient-K field with the adverse pressure sign. -/
noncomputable def vS (K t : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cl 2 y.2.1, cl 2 y.2.2, -(K * cl (max t 0 + 2) y.1 * cl 2 y.2.2) + 1 - cl 2 y.2.1 ^ 2)

/-- Slow entry from a zero wall shear: at some η > 0 the trajectory is in the region 0 ≤ p < 1,
q < 3(1 − p), f > 11/15, having had p < 1 on [0, η]. -/
def SlowS (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η > 0, (∀ s ∈ Icc 0 η, (Y s).2.1 < 1) ∧
    0 ≤ (Y η).2.1 ∧ (Y η).2.2 < 3 * (1 - (Y η).2.1) ∧ 11 / 15 < (Y η).1

/-- The certified chain shape: every solution of the clamped coefficient-K field on [0, T] from
(0, 0, 0) has the event `E`. -/
def ChainK (K : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →
    Y 0 = (0, 0, 0) → E Y

end Checked.FSSep.SBase
