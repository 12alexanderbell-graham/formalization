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

/-! Falkner–Skan adverse pressure gradient, the clamped field of the scaled adverse-sign problem and the two shooting events (slow approach and overshoot). Module `NBase`, promoted from `Work/FSNeg/NBase.lean`. -/

namespace Checked.FSNeg.NBase
open Set

/-- Clamp to [−c, c]. -/
noncomputable def cl (c y : ℝ) : ℝ := max (-c) (min c y)

/-- The clamped K = 10 field with the adverse pressure sign. -/
noncomputable def vN (t : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cl 2 y.2.1, cl 2 y.2.2, -(10 * cl (max t 0 + 2) y.1 * cl 2 y.2.2) + 1 - cl 2 y.2.1 ^ 2)

theorem cl_of_abs_le {c y : ℝ} (h : |y| ≤ c) : cl c y = y := by
  unfold cl
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

/-- Overshoot: p > 1 at some η > 0. -/
def Over (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η > 0, 1 < (Y η).2.1

/-- Slow: at some η > 0 the trajectory is in the region 0 ≤ p < 1, 0 < q < 3(1 − p), f > 11/30,
having had p < 1 and q > 0 on [0, η]. -/
def Slow (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η > 0, (∀ s ∈ Icc 0 η, (Y s).2.1 < 1 ∧ 0 < (Y s).2.2) ∧
    0 ≤ (Y η).2.1 ∧ (Y η).2.2 < 3 * (1 - (Y η).2.1) ∧ 11 / 30 < (Y η).1

end Checked.FSNeg.NBase
