import Mathlib

/-!
# Blind restatement: Lane-Emden equation of index 4

Reading choices:

* A solution is a function `θ : ℝ → ℝ`; only its values on `[0, 16]` matter.
* The equation `θ'' + (2/ξ) θ' + θ⁴ = 0` is required on the open interval `(0, 16)`
  (it is singular at `ξ = 0`, so not there). On this open interval `θ` is differentiable,
  `deriv θ` is differentiable, and
  `deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + θ ξ ^ 4 = 0`.
  The power is the literal `θ ^ 4` (natural number exponent), with no absolute value or
  positive-part truncation, so it stays valid where `θ` is negative (after the first zero,
  up to 16).
* Regularity at the centre: `θ` is continuous on `[0, 16]`, `θ 0 = 1`, and `θ` has
  one-sided derivative `0` at `0`, i.e. `HasDerivWithinAt θ 0 (Set.Ici 0) 0`.
* "First zero" means `ξ₁` is the least element of `{ξ ∈ [0, 16] | θ ξ = 0}`
  (`IsLeast`), so it exists in `[0, 16]` and `θ` has no zero in `[0, ξ₁)`.
* `ω₄ = -ξ₁² θ'(ξ₁)` uses `deriv θ ξ₁`; since `ξ₁ ∈ (0, 16)` (it lies near 14.97) this is the
  genuine two-sided derivative. The claim is stated directly with `ξ₁` and `deriv θ ξ₁`
  substituted for `ω₄` and in `ρ_c/ρ̄ = ξ₁³ / (3 ω₄)`.
* All numerical bounds are non-strict (`≤`), as in the claim, with decimal literals in `ℝ`.
* No uniqueness is assumed: the statement holds for every `θ` satisfying the hypotheses.
-/

namespace Work.Math.LaneEmden4Blind

theorem blind_laneEmden4 (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 16))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Ici 0) 0)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 16,
      DifferentiableAt ℝ θ ξ ∧ DifferentiableAt ℝ (deriv θ) ξ ∧
        deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + θ ξ ^ 4 = 0) :
    ∃ ξ₁ : ℝ,
      IsLeast {ξ : ℝ | ξ ∈ Set.Icc (0 : ℝ) 16 ∧ θ ξ = 0} ξ₁ ∧
      (14.97154634 ≤ ξ₁ ∧ ξ₁ ≤ 14.97154636) ∧
      (1.79722991 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 1.79722992) ∧
      (622.407879 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 622.407886) := by
  sorry

end Work.Math.LaneEmden4Blind
