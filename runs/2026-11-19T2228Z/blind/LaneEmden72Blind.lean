import Mathlib

/-!
# Lane–Emden equation, index 7/2 (blind restatement)

Reading choices.
* A solution is a function `θ : ℝ → ℝ`; only its values on `[0,10]` matter.
* Regularity at the centre: `θ` is continuous on `[0,10]`, `θ 0 = 1`, and `θ` has
  right-derivative `0` at `0` (`HasDerivWithinAt θ 0 (Set.Ici 0) 0`).
* The ODE is required at every `ξ` in the open interval `(0,10)` (where `2/ξ` makes sense),
  with `θ` differentiable there, `deriv θ` differentiable there, and
  `deriv (deriv θ) ξ + 2/ξ * deriv θ ξ + θ ξ ^ (7/2 : ℝ) = 0`.
* The power is Mathlib's `Real.rpow` with exponent `(7/2 : ℝ)`. For `θ < 0` it equals
  `exp(7/2 · log |θ|) · cos(7π/2) = 0`, and `0 ^ (7/2) = 0`; so beyond the first zero the
  nonlinearity is `0` (the usual convention `max θ 0 ^ (7/2)`). The claim only concerns
  the first zero, so this does not affect it.
* "First zero" `ξ₁`: `0 < ξ₁ ≤ 10`, `θ ξ₁ = 0`, and `θ ξ ≠ 0` for all `0 ≤ ξ < ξ₁`.
  (It is asserted to exist; it is then automatically unique.)
* `ω = -ξ₁^2 * deriv θ ξ₁` (θ is differentiable at `ξ₁ ∈ (0,10)` by hypothesis if `ξ₁ < 10`;
  `ξ₁ ≤ 10` is stated with the numeric bounds, which force `ξ₁ < 10`).
* `ρ_c/ρ̄ = ξ₁^3 / (3 ω)`.
* Constants are decimal literals in `ℝ`; all bounds are closed (`≤`).
* No uniqueness of `θ` is assumed: the statement quantifies over all such `θ`.
-/

namespace Work.Math.LaneEmden72Blind

theorem blind_laneEmden72 (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 10))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Ici 0) 0)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 10,
      DifferentiableAt ℝ θ ξ ∧ DifferentiableAt ℝ (deriv θ) ξ ∧
      deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + θ ξ ^ (7 / 2 : ℝ) = 0) :
    ∃ ξ₁ : ℝ, 0 < ξ₁ ∧ ξ₁ ≤ 10 ∧ θ ξ₁ = 0 ∧
      (∀ ξ, 0 ≤ ξ → ξ < ξ₁ → θ ξ ≠ 0) ∧
      (9.53580534 ≤ ξ₁ ∧ ξ₁ ≤ 9.53580535) ∧
      (1.89055709 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 1.89055710) ∧
      (152.8836627 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 152.8836632) := by
  sorry

end Work.Math.LaneEmden72Blind
