import Mathlib

/-!
# Lane–Emden equation of index 5/2 (blind restatement)

Reading choices.

* A solution is a function `θ : ℝ → ℝ` (only its values on `[0,6]` matter) such that
  - `θ` is `C²` on the closed interval `[0,6]` (`ContDiffOn ℝ 2 θ (Set.Icc 0 6)`), which is the
    natural meaning of "regular at the centre" together with the centre conditions;
  - `θ 0 = 1`;
  - `θ'(0) = 0`, written as the one-sided-in-`[0,6]` derivative `derivWithin θ (Set.Icc 0 6) 0 = 0`
    (θ is only considered on `[0,6]`, so the derivative at the endpoint 0 is taken within it);
  - the ODE `θ'' + (2/ξ) θ' + θ^(5/2) = 0` holds for every `ξ` in the open interval `(0,6)`
    (the equation is singular at `ξ = 0`, so it is not required there; at `ξ = 6` it follows by
    continuity of the C² data, so requiring it on `(0,6)` is equivalent to requiring it on `(0,6]`).
    On the open interval the ordinary `deriv` agrees with `derivWithin`.
* No uniqueness is assumed: the theorem is universally quantified over all such `θ`.
* The power `θ^(5/2)` is `Real.rpow (θ ξ) (5/2)`, with exponent `(5/2 : ℝ)`. Mathlib's convention
  for negative base `x` is `x ^ y = exp (log x * y) * cos (y * π)`; for `y = 5/2` the cosine is
  `cos (5π/2) = 0`, so `θ^(5/2) = 0` where `θ < 0` (and `0^(5/2) = 0`). This is the usual
  convention (the nonlinearity is only meaningful where `θ ≥ 0`). The first zero lies before any
  place where `θ < 0` matters, so the claim is insensitive to this choice.
* "First zero" `ξ₁`: `ξ₁ ∈ (0,6)`, `θ ξ₁ = 0` and `θ ξ > 0` for all `ξ ∈ [0, ξ₁)`. This
  characterizes `ξ₁` uniquely, so the theorem says that the first zero exists and has the stated
  bounds.
* Constants: `ω = -ξ₁² θ'(ξ₁)` with `θ'(ξ₁) = deriv θ ξ₁` (ξ₁ is interior, so this is unambiguous),
  and the central concentration is `ρ_c/ρ̄ = ξ₁³ / (3 ω)`.
* The numerical bounds are non-strict, exactly as in the claim.
-/

namespace Work.Math.LaneEmden52Blind

theorem blind_laneEmden52 (θ : ℝ → ℝ)
    (hC : ContDiffOn ℝ 2 θ (Set.Icc (0 : ℝ) 6))
    (h0 : θ 0 = 1)
    (h0' : derivWithin θ (Set.Icc (0 : ℝ) 6) 0 = 0)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 6,
      deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + (θ ξ) ^ ((5 : ℝ) / 2) = 0) :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0 : ℝ) 6 ∧ θ ξ₁ = 0 ∧
      (∀ ξ ∈ Set.Ico (0 : ℝ) ξ₁, 0 < θ ξ) ∧
      (5.35527545 ≤ ξ₁ ∧ ξ₁ ≤ 5.35527546) ∧
      (2.18719956 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 2.18719957) ∧
      (23.40646222 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 23.40646231) := by
  sorry

end Work.Math.LaneEmden52Blind
