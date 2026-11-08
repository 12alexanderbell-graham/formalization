import Mathlib

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index two

**Question.** The Lane–Emden equation of index two, θ'' + (2/ξ) θ' + θ² = 0 with θ(0) = 1
(regular at the singular point ξ = 0), has no closed-form solution. Its first zero ξ₁, the number
ω₂ = −ξ₁² θ'(ξ₁) (mass factor) and the central concentration ξ₁³/(3ω₂) are entries of the classical
table of polytropes (Chandrasekhar 1939, Table 4; Horedt 1986), computed there in floating point.
With index three (`Checked.Math.LaneEmden`, PROVED) this certifies a second row of that table with
the same simulator, now generic in the index (run 2026-11-08T0228Z).

**What is stated** (frozen before proof, run 2026-11-08T0228Z): `laneEmden2_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, ω₂ and ξ₁³/(3ω₂) printed in its statement.
θ'(0) = 0 is not assumed. Only Mathlib definitions occur in the statement. Existence of such a θ
is a separate theorem (to do).
-/

namespace Work.Math.LaneEmden2
open Set

/-- Lane–Emden equation of index 2: for every solution θ of θ'' + (2/ξ)θ' + θ² = 0 on (0, 5] with
θ(0) = 1, θ differentiable on [0, 5] with derivative φ, and φ continuous at 0, there is a first zero
ξ₁ of θ with 4.3528745959 ≤ ξ₁ ≤ 4.3528745960 (θ > 0 before it), at which −ξ₁² θ'(ξ₁) lies between
2.4110460120 and 2.4110460122 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 11.402542860 and
11.402542864. -/
theorem laneEmden2_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 5, HasDerivWithinAt θ (φ ξ) (Icc 0 5) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 5) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 5, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Icc 0 5) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.4110460122 ∧
      11.402542860 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 11.402542864 := by
  sorry

end Work.Math.LaneEmden2
