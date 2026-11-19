import Mathlib

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index five halves

**Question.** The Lane–Emden equation of index five halves, θ'' + (2/ξ) θ' + θ ^ (5/2) = 0 with
θ(0) = 1 (regular at the singular point ξ = 0), is a row of the classical tables of polytropes
(Chandrasekhar; Horedt), computed there in floating point. It has no closed-form solution. Its
first zero ξ₁, the mass factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass
factor) are the entries of that row. Indices two, three, four and three halves are certified
(`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`, `Checked.Math.LaneEmden4`,
`Checked.Math.LaneEmden32`); θ ^ (5/2) has no polynomial Taylor recursion and is not smooth at the
zero of θ (its second derivative in θ blows up there).

**What is stated** (frozen before proof, run 2026-11-19T1628Z): `laneEmden52_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. The power is Mathlib's real power `Real.rpow`;
for a negative base it returns zero at this exponent, so past the zero of θ the hypothesis reads
θ'' + (2/ξ) θ' = 0; the conclusions concern [0, ξ₁], where θ is not negative. Only Mathlib
definitions occur in the statement. Existence of such a θ is a separate theorem (to do).
-/

namespace Work.Math.LaneEmden52
open Set

/-- Lane–Emden equation of index 5/2: for every solution θ of θ'' + (2/ξ)θ' + θ ^ (5/2) = 0 on
(0, 6] with θ(0) = 1, θ differentiable on [0, 6] with derivative φ, and φ continuous at 0, there is
a first zero ξ₁ of θ with 5.35527545 ≤ ξ₁ ≤ 5.35527546 (θ > 0 before it), at which −ξ₁² θ'(ξ₁) lies
between 2.18719956 and 2.18719957 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 23.40646222 and
23.40646231. -/
theorem laneEmden52_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 6, HasDerivWithinAt θ (φ ξ) (Icc 0 6) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 6) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 6,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((5 : ℝ) / 2)) (Icc 0 6) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 5.35527545 ≤ ξ₁ ∧ ξ₁ ≤ 5.35527546 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.18719956 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.18719957 ∧
      23.40646222 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 23.40646231 := by
  sorry

end Work.Math.LaneEmden52
