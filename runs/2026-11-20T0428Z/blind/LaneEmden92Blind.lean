import Mathlib

/-!
# Lane–Emden, index 9/2 (blind restatement)

Reading choices.
* A solution is a function `θ : ℝ → ℝ` (only values on `[0,32]` matter).
* Regularity at the centre: `θ` is continuous on `[0,32]`, `θ 0 = 1`, and the right
  derivative at `0` exists and equals `0` (`HasDerivWithinAt θ 0 (Set.Ici 0) 0`).
* The ODE `θ'' + (2/ξ) θ' + θ^(9/2) = 0` is required at every `ξ ∈ (0,32)` (open interval; the
  singular point `0` and the endpoint `32` are excluded), with `θ` and `deriv θ` differentiable
  there, so `deriv (deriv θ)` is the genuine second derivative.
* `θ^(9/2)` is `Real.rpow (θ ξ) (9/2)` with exponent `(9/2 : ℝ)`. For negative base Mathlib gives
  `exp(log x · 9/2) · cos(9π/2) = 0`, so it agrees with the positive-part convention
  `max θ 0 ^ (9/2)`; this only matters beyond the first zero, which the conclusion does not use
  except through the ODE hypothesis.
* First zero: `ξ₁` is the least element of `{ξ ∈ [0,32] | θ ξ = 0}` (`IsLeast`).
* Constants: `ω = -ξ₁² θ'(ξ₁)` with `θ' = deriv θ`; `ρ_c/ρ̄ = ξ₁³/(3ω)`. The decimal bounds are
  stated as exact rational literals, with closed inequalities as in the claim.
* No uniqueness is assumed: the statement quantifies over every `θ` satisfying the hypotheses.
-/

namespace Work.Math.LaneEmden92Blind

theorem blind_laneEmden92 (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 32))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Ici 0) 0)
    (hdiff : ∀ ξ ∈ Set.Ioo (0 : ℝ) 32, DifferentiableAt ℝ θ ξ ∧ DifferentiableAt ℝ (deriv θ) ξ)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 32,
      deriv (deriv θ) ξ + (2 / ξ) * deriv θ ξ + (θ ξ) ^ ((9 : ℝ) / 2) = 0) :
    ∃ ξ₁ : ℝ, IsLeast {ξ : ℝ | ξ ∈ Set.Icc (0 : ℝ) 32 ∧ θ ξ = 0} ξ₁ ∧
      (31.836463 ≤ ξ₁ ∧ ξ₁ ≤ 31.836464) ∧
      (1.7377988 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 1.7377989) ∧
      (6189.4730 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 6189.4733) := by
  sorry

end Work.Math.LaneEmden92Blind
