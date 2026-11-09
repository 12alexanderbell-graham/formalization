import Mathlib

namespace Blind.FSTenthLimit

/-- `f, f1, f2, f3` stand for `f, f', f'', f'''`: derivatives are taken within `[0,∞)`
at every `η ≥ 0`, the Falkner–Skan ODE with `β = 1/10` holds at every `η ≥ 0`,
`f(0) = 0`, `f'(0) = 0` and `f'(η) → 1` as `η → ∞`. -/
def IsSolution (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → f3 x + f x * f2 x + (1 / 10 : ℝ) * (1 - f1 x ^ 2) = 0) ∧
  f 0 = 0 ∧ f1 0 = 0 ∧
  Filter.Tendsto f1 Filter.atTop (nhds 1)

/-- Claim 1: every solution has `0.5870352191 < f''(0) < 0.5870352193`. -/
theorem wall_shear_window (f f1 f2 f3 : ℝ → ℝ) (h : IsSolution f f1 f2 f3) :
    (5870352191 / 10000000000 : ℝ) < f2 0 ∧ f2 0 < (5870352193 / 10000000000 : ℝ) := by
  sorry

/-- Claim 2: any two solutions agree (with first and second derivatives) for all `η ≥ 0`. -/
theorem solution_unique (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (hf : IsSolution f f1 f2 f3) (hg : IsSolution g g1 g2 g3) :
    ∀ x : ℝ, 0 ≤ x → f x = g x ∧ f1 x = g1 x ∧ f2 x = g2 x := by
  sorry

end Blind.FSTenthLimit
