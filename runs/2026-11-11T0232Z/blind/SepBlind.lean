import Mathlib

/-!
Falkner–Skan separation profile.

Encoding choices:
* The unknown is `f : ℝ → ℝ`, required `ContDiff ℝ 3` globally (so `deriv` is meaningful);
  the ODE and all conditions are only imposed for `η ≥ 0`.
* Derivatives: `f' = deriv f`, `f'' = deriv (deriv f)`, `f''' = deriv (deriv (deriv f))`.
* "f'(η) → 1 as η → ∞": `Tendsto (deriv f) atTop (𝓝 1)`.
* "for all sufficiently large η": `∀ᶠ η in atTop`.
* Strict interval for β via two strict inequalities with exact rational literals.
-/

theorem blind_sep :
    ∃ β : ℝ, (-1988377351 / 10000000000 : ℝ) < β ∧ β < (-1988377350 / 10000000000 : ℝ) ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 3 f ∧
        (∀ η : ℝ, 0 ≤ η →
          deriv (deriv (deriv f)) η + f η * deriv (deriv f) η
            + β * (1 - (deriv f η) ^ 2) = 0) ∧
        f 0 = 0 ∧ deriv f 0 = 0 ∧
        Filter.Tendsto (deriv f) Filter.atTop (nhds 1) ∧
        deriv (deriv f) 0 = 0 ∧
        (∀ η : ℝ, 0 < η → 0 < deriv (deriv f) η) ∧
        (∀ M : ℝ, ∀ᶠ η in Filter.atTop, M * (1 - deriv f η) ≤ deriv (deriv f) η) := by
  sorry
