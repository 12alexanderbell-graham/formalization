import Mathlib

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index nine halves

**Question.** The Lane–Emden equation of index nine halves, θ'' + (2/ξ) θ' + θ ^ (9/2) = 0 with
θ(0) = 1 (regular at the singular point ξ = 0), is a row of the classical tables of polytropes
(Chandrasekhar; Horedt), computed there in floating point. It has no closed-form solution. Its
first zero ξ₁, the mass factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass
factor) are the entries of that row. Indices two, three, four, three halves, five halves and seven
halves are certified (`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`, `Checked.Math.LaneEmden4`,
`Checked.Math.LaneEmden32`, `Checked.Math.LaneEmden52`, `Checked.Math.LaneEmden72`); θ ^ (9/2) has no
polynomial Taylor recursion and is not smooth at the zero of θ (its fifth derivative in θ blows up
there). The first zero lies near 31.8, three times further out than at index seven halves.

**What is stated** (frozen before proof, run 2026-11-20T0428Z): `laneEmden92_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. The power is Mathlib's real power `Real.rpow`;
for a negative base it returns zero at this exponent, so past the zero of θ the hypothesis reads
θ'' + (2/ξ) θ' = 0; the conclusions concern [0, ξ₁], where θ is not negative. Only Mathlib
definitions occur in the statement. Existence of such a θ is a separate theorem (to do).
Reference (floating point, not evidence): `runs/2026-11-20T0428Z/scripts/ref92.py` (40 digits) and
`ref92b.py` (a second integrator).
-/

namespace Work.Math.LaneEmden92
open Set

/-- Lane–Emden equation of index 9/2: for every solution θ of θ'' + (2/ξ)θ' + θ ^ (9/2) = 0 on
(0, 32] with θ(0) = 1, θ differentiable on [0, 32] with derivative φ, and φ continuous at 0, there is
a first zero ξ₁ of θ with 31.836463 ≤ ξ₁ ≤ 31.836464 (θ > 0 before it), at which −ξ₁² θ'(ξ₁) lies
between 1.7377988 and 1.7377989 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 6189.4730 and
6189.4733. -/
theorem laneEmden92_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 32, HasDerivWithinAt θ (φ ξ) (Icc 0 32) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 32) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 32,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((9 : ℝ) / 2)) (Icc 0 32) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 31.836463 ≤ ξ₁ ∧ ξ₁ ≤ 31.836464 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.7377988 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.7377989 ∧
      6189.4730 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 6189.4733 := by
  sorry

end Work.Math.LaneEmden92
