import Mathlib

/-!
# K = 10 (Falkner–Skan β = 1/10, scaled) existence: the clamped field and the two shooting events (run 2026-11-08T2028Z, make_row.py)

`vH t y` is the coefficient-10 field (p, q, −10 f q − 1 + p²) for y = (f, p, q) with p and q clamped to
[−2, 2] and f to [−(t⁺ + 2), t⁺ + 2] (t⁺ = max t 0): bounded and Lipschitz on every [0, T], so it
has a global flow. `Under Y` and `Over Y` are the two shooting events of a trajectory
(`Work.FSTenth.k10_under`, `k10_over`); ported from `Work.Hiemenz.HExBase`.
-/

namespace Work.FSTenth.F10ExBase
open Set

/-- Clamp to [−c, c]. -/
noncomputable def cl (c y : ℝ) : ℝ := max (-c) (min c y)

/-- The clamped K = 10 (Falkner–Skan β = 1/10, scaled) field. -/
noncomputable def vH (t : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cl 2 y.2.1, cl 2 y.2.2, -(10 * cl (max t 0 + 2) y.1 * cl 2 y.2.2) - 1 + cl 2 y.2.1 ^ 2)

theorem cl_of_abs_le {c y : ℝ} (h : |y| ≤ c) : cl c y = y := by
  unfold cl
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

/-- Undershoot: q < 0 at some η > 0 while p < 1 on [0, η]. -/
def Under (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η > 0, (Y η).2.2 < 0 ∧ ∀ s ∈ Icc 0 η, (Y s).2.1 < 1

/-- Overshoot: p > 1 at some η > 0 while q > 0 on [0, η]. -/
def Over (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η > 0, 1 < (Y η).2.1 ∧ ∀ s ∈ Icc 0 η, 0 < (Y s).2.2

theorem not_under_and_over (Y : ℝ → ℝ × ℝ × ℝ) (hU : Under Y) (hO : Over Y) : False := by
  obtain ⟨a, ha, hqa, hpa⟩ := hU
  obtain ⟨b, hb, hpb, hqb⟩ := hO
  rcases le_total a b with h | h
  · have := hqb a ⟨ha.le, h⟩; linarith
  · have := hpa b ⟨hb.le, h⟩; linarith

end Work.FSTenth.F10ExBase
