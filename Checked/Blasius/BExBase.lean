import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
/-! Blasius boundary layer, `BExBase`: the Blasius field with its components clamped, globally Lipschitz on every bounded time interval. Promoted from `Work/Blasius/BExBase.lean`. -/

namespace Checked.Blasius.BExBase
open Set

/-- Clamp to [−c, c]. -/
noncomputable def cl (c y : ℝ) : ℝ := max (-c) (min c y)

/-- The clamped Blasius field. -/
noncomputable def vF (t : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cl 4 y.2.1, cl 2 y.2.2, -(cl (4 * max t 0 + 1) y.1 * cl 2 y.2.2 / 2))

theorem cl_of_abs_le {c y : ℝ} (h : |y| ≤ c) : cl c y = y := by
  unfold cl
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

end Checked.Blasius.BExBase
