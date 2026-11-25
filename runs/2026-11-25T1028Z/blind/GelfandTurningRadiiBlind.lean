import Mathlib

open Filter Topology Set

/-- The quantity `λ(s) = s² e^{w(s)}`. -/
noncomputable def gelfandLam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

theorem blind_gelfand_turning_radii
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hw : ∀ s, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      StrictMonoOn (gelfandLam w) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (gelfandLam w) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (gelfandLam w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, gelfandLam w (ζ (2 * k + 1)) < 2 ∧ 2 < gelfandLam w (ζ (2 * k))) ∧
      Tendsto (gelfandLam w) atTop (𝓝 2) ∧
      ζ 0 ∈ Icc (4.071496844 : ℝ) 4.071496845 ∧
      gelfandLam w (ζ 0) ∈ Icc (3.321992118 : ℝ) 3.321992119 ∧
      Tendsto (fun k : ℕ => (gelfandLam w (ζ (k + 1)) - 2) / (gelfandLam w (ζ k) - 2))
        atTop (𝓝 (-Real.exp (-Real.pi / Real.sqrt 7))) ∧
      -- (i)
      Tendsto (fun k : ℕ => ζ (k + 1) / ζ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      -- (ii)
      (∀ k : ℕ, 6 ≤ k →
        10.3 ≤ ζ (k + 1) / ζ k ∧ ζ (k + 1) / ζ k ≤ 11.2 ∧
        -0.33 ≤ (gelfandLam w (ζ (k + 1)) - 2) / (gelfandLam w (ζ k) - 2) ∧
        (gelfandLam w (ζ (k + 1)) - 2) / (gelfandLam w (ζ k) - 2) ≤ -0.28) := by
  sorry
