import Mathlib

open Set

/-- Dimensionless Bonnor–Ebert mass of the sphere truncated at radius `ξ`, for a profile `ψ`. -/
noncomputable def beMass (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-ψ ξ / 2) * ξ ^ 2 * deriv ψ ξ

/-- `ψ` is the regular solution of the isothermal Lane–Emden equation on `[0, ∞)`. -/
structure IsRegularEmdenSolution (ψ : ℝ → ℝ) : Prop where
  contDiff : ContDiffOn ℝ 2 ψ (Set.Ici 0)
  zero : ψ 0 = 0
  deriv_zero : derivWithin ψ (Set.Ici 0) 0 = 0
  ode : ∀ ξ : ℝ, 0 < ξ →
    (1 / ξ ^ 2) * deriv (fun x => x ^ 2 * deriv ψ x) ξ = Real.exp (-ψ ξ)

theorem blind_bonnor_ebert_third_max (ψ : ℝ → ℝ) (hψ : IsRegularEmdenSolution ψ) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ : ℝ,
      6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧
      7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧
      84497 ≤ ξ₅ ∧ ξ₅ ≤ 84516 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁) ∧
      (∀ ξ : ℝ, ξ₁ ≤ ξ → ξ ≠ ξ₂ → beMass ψ ξ₂ < beMass ψ ξ) ∧
      (∀ ξ : ℝ, ξ₂ ≤ ξ → ξ ≠ ξ₃ → beMass ψ ξ < beMass ψ ξ₃) ∧
      (∀ ξ : ℝ, ξ₃ ≤ ξ → ξ ≠ ξ₄ → beMass ψ ξ₄ < beMass ψ ξ) ∧
      (∀ ξ : ℝ, ξ₄ ≤ ξ → ξ ≠ ξ₅ → beMass ψ ξ < beMass ψ ξ₅) ∧
      0.80091 ≤ beMass ψ ξ₅ ∧ beMass ψ ξ₅ ≤ 0.800916 ∧
      3556300000 ≤ Real.exp (ψ ξ₅) ∧ Real.exp (ψ ξ₅) ≤ 3558000000 := by
  sorry
