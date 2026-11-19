import Mathlib

/-!
# Lane–Emden equation, index 3/2 (blind restatement)

Reading choices:

* A solution is a function `θ : ℝ → ℝ`; only its values on `[0,4]` matter.
* Regularity at the centre: `θ` is continuous on `[0,4]`, `θ 0 = 1`, and `θ` has
  one-sided (within `[0,4]`) derivative `0` at `0`.
* The ODE `θ'' + (2/ξ) θ' + θ^(3/2) = 0` is required at every `ξ ∈ (0,4)` (open interval,
  since `2/ξ` is singular at 0), with `θ` differentiable and `deriv θ` differentiable there,
  so `θ''` is `deriv (deriv θ)`. It is required also past the first zero.
* The power `θ ξ ^ (3/2 : ℝ)` is `Real.rpow`. For `θ ξ < 0`, Mathlib's convention is
  `exp (log x * y) * cos (y * π)`, and `cos (3π/2) = 0`, so the term is `0` there
  (the usual `θ₊^n` convention). For `θ ξ = 0` it is `0`.
* First zero `ξ₁`: the least element (`IsLeast`) of `{ξ ∈ [0,4] | θ ξ = 0}`.
* `ω := -ξ₁² * deriv θ ξ₁` (two-sided derivative; `ξ₁ < 4` follows from the bounds),
  and `ρ_c/ρ̄ := ξ₁³ / (3 ω)`. Decimal bounds are the literal rationals as given.
* No uniqueness is assumed: the statement quantifies over every such `θ`.
-/

namespace Work.Math.LaneEmden32Blind

theorem blind_laneEmden32 (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 4))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Icc 0 4) 0)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 4,
      DifferentiableAt ℝ θ ξ ∧ DifferentiableAt ℝ (deriv θ) ξ ∧
      deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + (θ ξ) ^ (3 / 2 : ℝ) = 0) :
    ∃ ξ₁ : ℝ, IsLeast {ξ : ℝ | ξ ∈ Set.Icc (0 : ℝ) 4 ∧ θ ξ = 0} ξ₁ ∧
      3.65375373 ≤ ξ₁ ∧ ξ₁ ≤ 3.65375374 ∧
      (2.71405511 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 2.71405513) ∧
      (5.99070450 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 5.99070453) := by
  sorry

end Work.Math.LaneEmden32Blind
