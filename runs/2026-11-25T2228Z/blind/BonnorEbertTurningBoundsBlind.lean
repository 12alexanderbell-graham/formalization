import Mathlib

open Filter Topology Set Real

/-- Dimensionless pressure-confined mass for a profile with derivative `φ`. -/
noncomputable def beMass (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

theorem blind_bonnor_ebert_turning_bounds
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hw : ∀ s, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ξ : ℕ → ℝ,
      StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      -- monotonicity pieces
      StrictMonoOn (beMass w φ) (Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (beMass w φ) (Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (beMass w φ) (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      -- global / tail extremality
      (∀ s, 0 ≤ s → beMass w φ s ≤ beMass w φ (ξ 0)) ∧
      (∀ k : ℕ, ∀ s, ξ (2 * k) ≤ s → s ≠ ξ (2 * k + 1) →
        beMass w φ (ξ (2 * k + 1)) < beMass w φ s) ∧
      (∀ k : ℕ, ∀ s, ξ (2 * k + 1) ≤ s → s ≠ ξ (2 * k + 2) →
        beMass w φ s < beMass w φ (ξ (2 * k + 2))) ∧
      -- position relative to the singular isothermal value
      (∀ k : ℕ, beMass w φ (ξ (2 * k + 1)) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) < beMass w φ (ξ (2 * k))) ∧
      Tendsto (beMass w φ) atTop (𝓝 (Real.sqrt (2 / Real.pi))) ∧
      (6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515) ∧
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop
        (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
          (beMass w φ (ξ (k + 1)) - Real.sqrt (2 / Real.pi)) /
          (beMass w φ (ξ k) - Real.sqrt (2 / Real.pi))) atTop
        (𝓝 (-Real.exp (-Real.pi / Real.sqrt 7))) ∧
      -- explicit bounds from the sixth extremum on
      (∀ k : ℕ, 5 ≤ k → ξ (k + 1) / ξ k ∈ Icc (9.2 : ℝ) 12.9) ∧
      (∀ k : ℕ, 5 ≤ k →
        (beMass w φ (ξ (k + 1)) - Real.sqrt (2 / Real.pi)) /
          (beMass w φ (ξ k) - Real.sqrt (2 / Real.pi)) ∈ Icc (-0.42 : ℝ) (-0.21)) := by
  sorry
