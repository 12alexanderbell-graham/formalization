import Mathlib

open Filter Set Real

namespace BonnorEbertBlind

/-- `ψ` is the regular solution of the isothermal Lane–Emden equation on `[0, ∞)`:
`ψ(0) = 0`, `ψ'(0) = 0` (one-sided derivative), and for `ξ > 0`,
`(ξ² ψ')' = ξ² e^{-ψ}`. -/
def IsRegularSolution (ψ : ℝ → ℝ) : Prop :=
  ContinuousOn ψ (Ici 0) ∧
  ψ 0 = 0 ∧
  HasDerivWithinAt ψ 0 (Ici 0) 0 ∧
  (∀ ξ : ℝ, 0 < ξ → DifferentiableAt ℝ ψ ξ) ∧
  (∀ ξ : ℝ, 0 < ξ →
    HasDerivAt (fun x => x ^ 2 * deriv ψ x) (ξ ^ 2 * Real.exp (-ψ ξ)) ξ)

/-- Dimensionless mass of the truncated sphere of radius `ξ`. -/
noncomputable def mass (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ((4 * Real.pi) ^ (-(1 : ℝ) / 2)) * Real.exp (-ψ ξ / 2) * ξ ^ 2 * deriv ψ ξ

theorem blind_bonnor_ebert_all_extrema (ψ : ℝ → ℝ) (hψ : IsRegularSolution ψ) :
    ∃ x : ℕ → ℝ,
      StrictMono x ∧
      Tendsto x atTop atTop ∧
      (6.4507514 : ℝ) ≤ x 0 ∧ x 0 ≤ 6.4507515 ∧
      -- (i) global maximum at x 0
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ x 0 → mass ψ ξ < mass ψ (x 0)) ∧
      -- (ii) minima at odd indices
      (∀ k : ℕ, ∀ ξ : ℝ, x (2 * k) ≤ ξ → ξ ≠ x (2 * k + 1) →
        mass ψ (x (2 * k + 1)) < mass ψ ξ) ∧
      -- (iii) maxima at later even indices
      (∀ k : ℕ, ∀ ξ : ℝ, x (2 * k + 1) ≤ ξ → ξ ≠ x (2 * k + 2) →
        mass ψ ξ < mass ψ (x (2 * k + 2))) ∧
      -- (iv) minima below, maxima above, √(2/π)
      (∀ k : ℕ, mass ψ (x (2 * k + 1)) < Real.sqrt (2 / Real.pi)) ∧
      (∀ k : ℕ, Real.sqrt (2 / Real.pi) < mass ψ (x (2 * k))) ∧
      -- (v) limit
      Tendsto (mass ψ) atTop (nhds (Real.sqrt (2 / Real.pi))) := by
  sorry

end BonnorEbertBlind
