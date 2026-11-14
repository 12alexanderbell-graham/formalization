import Mathlib

/-! Blind restatement of the second-maximum Bonnor–Ebert claim (run 2026-11-14T1028Z; Sonnet, brief `runs/2026-11-14T1028Z/blind/BRIEF.md`), copied verbatim from `runs/2026-11-14T1028Z/blind/BonnorEbertMax2Blind.lean` inside a namespace. -/

namespace Work.Math.BonnorEbertMax2Blind

open Set Real

/-- Dimensionless Bonnor–Ebert mass `m(ξ) = (4π)^(-1/2) e^(-ψ(ξ)/2) ξ² ψ'(ξ)`,
with `ψ'` taken as the derivative within `[0, ∞)` (so it is meaningful at `ξ = 0`). -/
noncomputable def beMass (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * Real.exp (-(ψ ξ) / 2) * ξ ^ 2 * derivWithin ψ (Ici 0) ξ

theorem blind_bonnor_ebert_second_max (ψ : ℝ → ℝ)
    (hsmooth : ContDiffOn ℝ 2 ψ (Ici 0))
    (h0 : ψ 0 = 0)
    (h0' : HasDerivWithinAt ψ 0 (Ici 0) 0)
    (hode : ∀ ξ : ℝ, 0 < ξ →
      deriv (fun x => x ^ 2 * derivWithin ψ (Ici 0) x) ξ = ξ ^ 2 * Real.exp (-(ψ ξ))) :
    ∃ ξ₁ ξ₂ ξ₃ : ℝ,
      6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁) ∧
      (∀ ξ : ℝ, ξ₁ ≤ ξ → ξ ≠ ξ₂ → beMass ψ ξ₂ < beMass ψ ξ) ∧
      (∀ ξ : ℝ, ξ₂ ≤ ξ → ξ ≠ ξ₃ → beMass ψ ξ < beMass ψ ξ₃) ∧
      0.8306 ≤ beMass ψ ξ₃ ∧ beMass ψ ξ₃ ≤ 0.8308 ∧
      258300 ≤ Real.exp (ψ ξ₃) ∧ Real.exp (ψ ξ₃) ≤ 258800 := by
  sorry

end Work.Math.BonnorEbertMax2Blind
