import Mathlib

open Filter Topology Set

noncomputable section

/-- Dimensionless pressure-confined mass at radius `s`, for a solution `w` with derivative `φ`. -/
def beMass (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

/-- Mass of the singular isothermal sphere. -/
def singularMass : ℝ := Real.sqrt (2 / Real.pi)

theorem blind_bonnor_ebert_turning_ratio
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hw : ∀ s, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ξ : ℕ → ℝ,
      StrictMono ξ ∧
      Tendsto ξ atTop atTop ∧
      StrictMonoOn (beMass w φ) (Icc 0 (ξ 0)) ∧
      (∀ k, StrictAntiOn (beMass w φ) (Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k, StrictMonoOn (beMass w φ) (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      (∀ s, 0 ≤ s → beMass w φ s ≤ beMass w φ (ξ 0)) ∧
      (∀ k, ∀ s, ξ (2 * k) ≤ s → s ≠ ξ (2 * k + 1) →
        beMass w φ (ξ (2 * k + 1)) < beMass w φ s) ∧
      (∀ k, ∀ s, ξ (2 * k + 1) ≤ s → s ≠ ξ (2 * k + 2) →
        beMass w φ s < beMass w φ (ξ (2 * k + 2))) ∧
      (∀ k, beMass w φ (ξ (2 * k + 1)) < singularMass ∧
            singularMass < beMass w φ (ξ (2 * k))) ∧
      Tendsto (beMass w φ) atTop (𝓝 singularMass) ∧
      ξ 0 ∈ Icc (6.4507514 : ℝ) 6.4507515 ∧
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop
        (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
          (beMass w φ (ξ (k + 1)) - singularMass) / (beMass w φ (ξ k) - singularMass))
        atTop (𝓝 (-Real.exp (-Real.pi / Real.sqrt 7))) := by
  sorry

end
