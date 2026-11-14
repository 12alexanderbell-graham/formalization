import Mathlib

/-! Blind restatement of the second-minimum Bonnor–Ebert claim (run 2026-11-14T1428Z; Sonnet, brief `runs/2026-11-14T1428Z/blind/BRIEF.md`), copied verbatim from `runs/2026-11-14T1428Z/blind/BonnorEbertMin2Blind.lean` inside a namespace. -/

namespace Work.Math.BonnorEbertMin2Blind

open Real

/-- Dimensionless mass of a Bonnor–Ebert sphere truncated at radius `ξ`:
`m(ξ) = (4π)^{-1/2} e^{-ψ(ξ)/2} ξ² ψ'(ξ)`. -/
noncomputable def beMass (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-(ψ ξ) / 2) * ξ ^ 2 * deriv ψ ξ

/-- `ψ` is the regular solution of the isothermal Lane–Emden equation
`(1/ξ²) (ξ² ψ')' = e^{-ψ}` on `[0, ∞)` with `ψ(0) = 0`, `ψ'(0) = 0`. -/
structure IsRegularIsothermalSolution (ψ : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 2 ψ (Set.Ici 0)
  init_val : ψ 0 = 0
  init_deriv : HasDerivWithinAt ψ 0 (Set.Ici 0) 0
  ode : ∀ ξ : ℝ, 0 < ξ →
    HasDerivAt (fun x => x ^ 2 * deriv ψ x) (ξ ^ 2 * Real.exp (-(ψ ξ))) ξ

theorem blind_bonnor_ebert_second_min (ψ : ℝ → ℝ) (hψ : IsRegularIsothermalSolution ψ) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ : ℝ,
      6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧
      7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁) ∧
      (∀ ξ : ℝ, ξ₁ ≤ ξ → ξ ≠ ξ₂ → beMass ψ ξ₂ < beMass ψ ξ) ∧
      (∀ ξ : ℝ, ξ₂ ≤ ξ → ξ ≠ ξ₃ → beMass ψ ξ < beMass ψ ξ₃) ∧
      (∀ ξ : ℝ, ξ₃ ≤ ξ → ξ ≠ ξ₄ → beMass ψ ξ₄ < beMass ψ ξ) ∧
      0.787992 ≤ beMass ψ ξ₄ ∧ beMass ψ ξ₄ ≤ 0.787995 ∧
      31193900 ≤ Real.exp (ψ ξ₄) ∧ Real.exp (ψ ξ₄) ≤ 31196100 := by
  sorry

end Work.Math.BonnorEbertMin2Blind
