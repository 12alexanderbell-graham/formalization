import Mathlib

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index four

**Question.** The Lane–Emden equation of index four, θ'' + (2/ξ) θ' + θ ^ 4 = 0 with θ(0) = 1
(regular at the singular point ξ = 0), has no closed-form solution. Its first zero ξ₁, the mass
factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass factor) are entries of the
classical tables of polytropes (Chandrasekhar; Horedt), computed there in floating point. With
indices two and three (`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`) this certifies a third
row of those tables with the same validated simulator, generic in the index; the zero lies about
three times further out than for index three, so errors grow over a much longer interval.

**What is stated** (frozen before proof, run 2026-11-19T0428Z): `laneEmden4_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. Only Mathlib definitions occur in the
statement. Existence of such a θ is a separate theorem (to do).
-/

namespace Work.Math.LaneEmden4
open Set

/-- Lane–Emden equation of index 4: for every solution θ of θ'' + (2/ξ)θ' + θ⁴ = 0 on (0, 16] with
θ(0) = 1, θ differentiable on [0, 16] with derivative φ, and φ continuous at 0, there is a first
zero ξ₁ of θ with 14.97154634 ≤ ξ₁ ≤ 14.97154636 (θ > 0 before it), at which −ξ₁² θ'(ξ₁) lies
between 1.79722991 and 1.79722992 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 622.407879 and
622.407886. -/
theorem laneEmden4_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 16, HasDerivWithinAt θ (φ ξ) (Icc 0 16) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 16) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 16, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 4) (Icc 0 16) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 14.97154634 ≤ ξ₁ ∧ ξ₁ ≤ 14.97154636 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.79722991 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.79722992 ∧
      622.407879 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 622.407886 := by
  sorry

end Work.Math.LaneEmden4
