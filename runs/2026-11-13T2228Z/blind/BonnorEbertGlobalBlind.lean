import Mathlib

open Real Set

/-- Dimensionless Bonnor–Ebert mass of a sphere truncated at radius `ξ`,
for a profile `ψ`: `m(ξ) = (4π)^{-1/2} e^{-ψ(ξ)/2} ξ² ψ'(ξ)`. -/
noncomputable def beMass (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * Real.exp (-(ψ ξ) / 2) * ξ ^ 2 * deriv ψ ξ

/-- Regular solution of the isothermal Lane–Emden equation on `[0, ∞)`:
`(1/ξ²) (ξ² ψ')' = e^{-ψ}` for `ξ > 0`, `ψ(0) = 0`, `ψ'(0) = 0` (one-sided),
with `ψ` twice continuously differentiable up to the boundary `ξ = 0`. -/
theorem blind_bonnor_ebert_global
    (ψ : ℝ → ℝ)
    (hC : ContDiffOn ℝ 2 ψ (Set.Ici 0))
    (h0 : ψ 0 = 0)
    (h0' : HasDerivWithinAt ψ 0 (Set.Ici 0) 0)
    (hode : ∀ ξ : ℝ, 0 < ξ →
      deriv (fun x => x ^ 2 * deriv ψ x) ξ = ξ ^ 2 * Real.exp (-(ψ ξ))) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      1.1822265 ≤ beMass ψ ξ₁ ∧ beMass ψ ξ₁ ≤ 1.1822266 ∧
      ∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁ := by
  sorry
