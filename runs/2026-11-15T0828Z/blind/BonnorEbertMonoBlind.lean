import Mathlib

open Filter Set Real

/-- Dimensionless Bonnor–Ebert mass at truncation radius `ξ`, given `ψ` and its derivative `dψ`. -/
noncomputable def beMass (ψ dψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-(ψ ξ) / 2) * ξ ^ 2 * dψ ξ

theorem blind_bonnor_ebert_mono
    (ψ dψ : ℝ → ℝ)
    (h0 : ψ 0 = 0)
    (hd0 : dψ 0 = 0)
    (hψ : ∀ ξ, 0 ≤ ξ → HasDerivWithinAt ψ (dψ ξ) (Set.Ici 0) ξ)
    (hode : ∀ ξ, 0 ≤ ξ →
      HasDerivWithinAt (fun x => x ^ 2 * dψ x) (ξ ^ 2 * Real.exp (-(ψ ξ))) (Set.Ici 0) ξ) :
    ∃ ξ : ℕ → ℝ,
      StrictMono ξ ∧
      Tendsto ξ atTop atTop ∧
      (6.4507514 : ℝ) ≤ ξ 0 ∧ ξ 0 ≤ (6.4507515 : ℝ) ∧
      (∀ x : ℝ, 0 ≤ x → x ≠ ξ 0 → beMass ψ dψ x < beMass ψ dψ (ξ 0)) ∧
      (∀ k : ℕ, ∀ x : ℝ, ξ (2 * k) ≤ x → x ≠ ξ (2 * k + 1) →
        beMass ψ dψ (ξ (2 * k + 1)) < beMass ψ dψ x) ∧
      (∀ k : ℕ, ∀ x : ℝ, ξ (2 * k + 1) ≤ x → x ≠ ξ (2 * k + 2) →
        beMass ψ dψ x < beMass ψ dψ (ξ (2 * k + 2))) ∧
      (∀ k : ℕ, beMass ψ dψ (ξ (2 * k + 1)) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) < beMass ψ dψ (ξ (2 * k))) ∧
      Tendsto (beMass ψ dψ) atTop (nhds (Real.sqrt (2 / Real.pi))) ∧
      StrictMonoOn (beMass ψ dψ) (Set.Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (beMass ψ dψ) (Set.Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (beMass ψ dψ) (Set.Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) := by
  sorry
