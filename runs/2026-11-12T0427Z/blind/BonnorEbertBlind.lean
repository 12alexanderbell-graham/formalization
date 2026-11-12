import Mathlib

open Real Set

/-- Dimensionless Bonnor–Ebert mass
`m(ξ) = (4π)^{-1/2} e^{-ψ(ξ)/2} ξ² ψ'(ξ)`, where `ψ'` is passed as `dψ`. -/
noncomputable def beMass (ψ dψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * Real.exp (-(ψ ξ) / 2) * ξ ^ 2 * dψ ξ

/-- `ψ` is the regular solution of the isothermal Lane–Emden equation
`ψ'' + (2/ξ) ψ' = e^{-ψ}` on `(0, ∞)`, with `dψ` its derivative, `ψ(0)=0`, `ψ'(0)=0`,
and `ψ`, `ψ'` continuous from the right at `0`. -/
structure IsRegularIsothermal (ψ dψ : ℝ → ℝ) : Prop where
  psi_zero : ψ 0 = 0
  dpsi_zero : dψ 0 = 0
  psi_cont : ContinuousWithinAt ψ (Ici 0) 0
  dpsi_cont : ContinuousWithinAt dψ (Ici 0) 0
  hasDeriv : ∀ ξ : ℝ, 0 < ξ → HasDerivAt ψ (dψ ξ) ξ
  hasDeriv2 : ∀ ξ : ℝ, 0 < ξ →
    HasDerivAt dψ (Real.exp (-(ψ ξ)) - 2 / ξ * dψ ξ) ξ

theorem blind_bonnor_ebert (ψ dψ : ℝ → ℝ) (h : IsRegularIsothermal ψ dψ) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      StrictMonoOn (beMass ψ dψ) (Icc 0 ξ₁) ∧
      StrictAntiOn (beMass ψ dψ) (Icc ξ₁ 7) ∧
      1.1822265 ≤ beMass ψ dψ ξ₁ ∧ beMass ψ dψ ξ₁ ≤ 1.1822266 ∧
      14.042032 ≤ Real.exp (ψ ξ₁) ∧ Real.exp (ψ ξ₁) ≤ 14.042033 := by
  sorry
