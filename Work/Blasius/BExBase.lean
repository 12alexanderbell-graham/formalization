import Mathlib

/-!
# Blasius existence: the clamped field (run 2026-11-07T1228Z)

`vF t y` is the Blasius field (p, q, −g q/2) with p clamped to [−4, 4], q to [−2, 2] and g to
[−(4t⁺ + 1), 4t⁺ + 1] (t⁺ = max t 0): bounded and Lipschitz on every [0, n], so it has a global
flow; the clamps are inactive along the flow from (0, 0, 1) (`Work/Blasius/BExBounds.lean`).
-/

namespace Work.Blasius.BExBase
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

end Work.Blasius.BExBase
