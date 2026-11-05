import Mathlib

/-!
# Mathematics (THE RESULT part 5): the constants of the Lane–Emden polytrope of index 3,
# certified

**Question.** The Lane–Emden equation of index 3,
  θ'' + (2/ξ) θ' + θ³ = 0,  θ(0) = 1,
(regular at the singular point ξ = 0) has no closed-form solution. Its first zero ξ₁ and the
number ω₃ = −ξ₁² θ'(ξ₁) are classical constants: ω₃ is the numerical factor of the Chandrasekhar
mass (Chandrasekhar 1939 prints 2.01824), ξ₁ (printed 6.89685) fixes the radius of Eddington's
standard model, and ξ₁³/(3ω₃) is its central concentration ρ_c/ρ̄ (printed 54.18). Every value
in the literature found by the screen of run 2026-11-05T0028Z (Chandrasekhar 1939; Horedt 1986
tables; Boyd 2011 spectral, ≥ 10 digits) comes from floating-point computation; the screen found
no rigorous enclosure. So the answer to "are the printed digits right, and what are the next
ones, proved?" was not in print.

**What is stated here** (frozen before proof, annex 40.1). For every θ on [0, 7] that is
differentiable on [0, 7] with derivative φ (one-sided at the ends), with φ continuous at 0, φ
differentiable on (0, 7] with φ' = −(2/ξ)φ − θ³, and θ(0) = 1: θ has a zero ξ₁ with
6.896848615 ≤ ξ₁ ≤ 6.896848625, θ > 0 on [0, ξ₁) (so ξ₁ is the first zero), and
2.018235945 ≤ −ξ₁² φ(ξ₁) ≤ 2.018235955 and 54.1824805 ≤ ξ₁³ / (3 · (−ξ₁² φ(ξ₁))) ≤ 54.1824815.
θ'(0) = 0 is not assumed: it follows (the solution is bounded at the singular point).
Existence of such a θ is a separate statement (not yet stated: the singular point needs its own
fixed-point argument).

Only Mathlib definitions occur in the statement (no program definition to pin).
-/

namespace Work.Math.LaneEmden
open Set

/-- Lane–Emden equation of index 3: for every solution θ of θ'' + (2/ξ)θ' + θ³ = 0 on (0, 7] with
θ(0) = 1, θ differentiable on [0, 7] with derivative φ, and φ continuous at 0, the first zero
ξ₁ of θ satisfies 6.896848615 ≤ ξ₁ ≤ 6.896848625, the Chandrasekhar-mass constant
−ξ₁² θ'(ξ₁) lies between 2.018235945 and 2.018235955, and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between
54.1824805 and 54.1824815. -/
theorem laneEmden3_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 7) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 6.896848615 ≤ ξ₁ ∧ ξ₁ ≤ 6.896848625 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955 ∧
      54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815 := by
  sorry

end Work.Math.LaneEmden
