import Mathlib

/-!
# K = 10 with the adverse pressure sign (Falkner–Skan β = −1/10, scaled): the clamped field and the
# two shooting events (run 2026-11-09T0828Z)

`vN t y` is the field (p, q, −10 f q + 1 − p²) for y = (f, p, q) with p and q clamped to [−2, 2] and f
to [−(t⁺ + 2), t⁺ + 2] (t⁺ = max t 0), as `Work.FSTenth.F10ExBase.vH` with the pressure sign reversed.
Scaling: F(s) = c f(s/c), c = √(1/10), turns f''' + f f'' − (1 − f'²)/10 = 0 into
F''' + 10 F F'' + 1 − F'² = 0 (`Checked.FalknerSkan.FSScale.scale`).
`Over Y`: p > 1 somewhere. `Slow Y`: entry into the forward-invariant region
{0 ≤ p < 1, 0 < q < 3(1 − p), f > 11/30} with p < 1 and q > 0 before
(`runs/2026-11-09T0428Z/research/fs_negative_beta.md` §3.1–3.2, μ = 3, θ = 11/30).
-/

namespace Work.FSNeg.NBase
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

end Work.FSNeg.NBase
