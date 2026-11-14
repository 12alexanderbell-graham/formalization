import Mathlib

/-! Blind restatement of the first-minimum Bonnor–Ebert claim (run 2026-11-14T0428Z; Sonnet, brief `runs/2026-11-14T0428Z/blind/BRIEF.md`), copied verbatim from `runs/2026-11-14T0428Z/blind/BonnorEbertMinBlind.lean` inside a namespace. -/

namespace Work.Math.BonnorEbertMinBlind

open Real Set

/-- Dimensionless Bonnor–Ebert mass of the sphere truncated at radius `ξ`:
`m(ξ) = (4π)^(-1/2) * exp(-ψ(ξ)/2) * ξ^2 * ψ'(ξ)`. -/
noncomputable def beMass (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * Real.exp (-ψ ξ / 2) * ξ ^ 2 * deriv ψ ξ

/-- `ψ` is the regular solution of the isothermal Lane–Emden equation on `[0, ∞)`:
`C²` on `[0,∞)`, `ψ(0) = 0`, `ψ'(0) = 0`, and `(ξ² ψ')' = ξ² e^{-ψ}` for `ξ > 0`
(equivalently `(1/ξ²)(ξ² ψ')' = e^{-ψ}`). -/
def IsRegularEmden (ψ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 ψ (Set.Ici 0) ∧
  ψ 0 = 0 ∧
  HasDerivWithinAt ψ 0 (Set.Ici 0) 0 ∧
  ∀ ξ : ℝ, 0 < ξ →
    deriv (fun s => s ^ 2 * deriv ψ s) ξ = ξ ^ 2 * Real.exp (-ψ ξ)

theorem blind_bonnor_ebert_min (ψ : ℝ → ℝ) (hψ : IsRegularEmden ψ) :
    ∃ ξ₁ ξ₂ : ℝ,
      6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁) ∧
      (∀ ξ : ℝ, ξ₁ ≤ ξ → ξ ≠ ξ₂ → beMass ψ ξ₂ < beMass ψ ξ) ∧
      0.694366 ≤ beMass ψ ξ₂ ∧ beMass ψ ξ₂ ≤ 0.694367 ∧
      2579.69 ≤ Real.exp (ψ ξ₂) ∧ Real.exp (ψ ξ₂) ≤ 2579.71 := by
  sorry

end Work.Math.BonnorEbertMinBlind
