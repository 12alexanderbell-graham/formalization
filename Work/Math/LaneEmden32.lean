import Mathlib

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index three halves

**Question.** The Lane–Emden equation of index three halves, θ'' + (2/ξ) θ' + θ ^ (3/2) = 0 with
θ(0) = 1 (regular at the singular point ξ = 0), is the polytrope of a fully convective star and of
a cold non-relativistic degenerate gas. It has no closed-form solution. Its first zero ξ₁, the mass
factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass factor) are entries of the
classical tables of polytropes (Chandrasekhar; Horedt), computed there in floating point. Indices
two, three and four are certified (`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`,
`Checked.Math.LaneEmden4`); a fractional index is new for the simulator: θ ^ (3/2) has no
polynomial Taylor recursion and is not smooth at the zero of θ.

**What is stated** (frozen before proof, run 2026-11-19T1028Z): `laneEmden32_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. The power is Mathlib's real power `Real.rpow`;
for a negative base it returns zero at this exponent, so past the zero of θ the hypothesis reads
θ'' + (2/ξ) θ' = 0; the conclusions concern [0, ξ₁], where θ is not negative. Only Mathlib
definitions occur in the statement. Existence of such a θ is a separate theorem (to do).
-/

namespace Work.Math.LaneEmden32
open Set

/-- Lane–Emden equation of index 3/2: for every solution θ of θ'' + (2/ξ)θ' + θ ^ (3/2) = 0 on
(0, 4] with θ(0) = 1, θ differentiable on [0, 4] with derivative φ, and φ continuous at 0, there is
a first zero ξ₁ of θ with 3.65375373 ≤ ξ₁ ≤ 3.65375374 (θ > 0 before it), at which −ξ₁² θ'(ξ₁) lies
between 2.71405511 and 2.71405513 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 5.99070450 and
5.99070453. -/
theorem laneEmden32_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 4, HasDerivWithinAt θ (φ ξ) (Icc 0 4) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 4) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 4,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((3 : ℝ) / 2)) (Icc 0 4) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 3.65375373 ≤ ξ₁ ∧ ξ₁ ≤ 3.65375374 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.71405511 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.71405513 ∧
      5.99070450 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 5.99070453 := by
  sorry

end Work.Math.LaneEmden32
