import Mathlib

open Filter Set Real

namespace BonnorEbertBlind

/-- Dimensionless pressure-confined mass `m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π)`,
where `φ = w'`. -/
noncomputable def mass (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

/-- Mass of the singular isothermal sphere. -/
noncomputable def singularMass : ℝ := Real.sqrt (2 / Real.pi)

end BonnorEbertBlind

open BonnorEbertBlind in
theorem blind_bonnor_ebert_turning_decay
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hwd : ∀ s ∈ Set.Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Set.Ici (0 : ℝ)) s)
    (hφ0 : ContinuousWithinAt φ (Set.Ici (0 : ℝ)) 0)
    (hφd : ∀ s : ℝ, 0 < s →
      HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ξ : ℕ → ℝ,
      StrictMono ξ ∧
      Tendsto ξ atTop atTop ∧
      -- monotonicity pattern
      StrictMonoOn (mass w φ) (Set.Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (mass w φ) (Set.Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (mass w φ) (Set.Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      -- global / tail extremality
      IsMaxOn (mass w φ) (Set.Ici 0) (ξ 0) ∧
      (∀ k : ℕ, ∀ s ∈ Set.Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        mass w φ (ξ (2 * k + 1)) < mass w φ s) ∧
      (∀ k : ℕ, ∀ s ∈ Set.Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        mass w φ s < mass w φ (ξ (2 * k + 2))) ∧
      -- comparison with the singular isothermal sphere
      (∀ k : ℕ, mass w φ (ξ (2 * k + 1)) < singularMass ∧
        singularMass < mass w φ (ξ (2 * k))) ∧
      Tendsto (mass w φ) atTop (nhds singularMass) ∧
      -- first maximum
      (6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515) ∧
      -- asymptotic ratios
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop
        (nhds (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
          (mass w φ (ξ (k + 1)) - singularMass) / (mass w φ (ξ k) - singularMass))
        atTop (nhds (-Real.exp (-Real.pi / Real.sqrt 7))) ∧
      -- uniform bounds from index 5
      (∀ k : ℕ, 5 ≤ k →
        (9.2 ≤ ξ (k + 1) / ξ k ∧ ξ (k + 1) / ξ k ≤ 12.9) ∧
        (-0.42 ≤ (mass w φ (ξ (k + 1)) - singularMass) / (mass w φ (ξ k) - singularMass) ∧
          (mass w φ (ξ (k + 1)) - singularMass) / (mass w φ (ξ k) - singularMass) ≤ -0.21)) ∧
      -- geometric decay of the errors
      (∀ n : ℕ,
        |ξ (n + 6) / ξ (n + 5) - Real.exp (2 * Real.pi / Real.sqrt 7)|
            ≤ (23 / 10 : ℝ) * (21 / 50 : ℝ) ^ n ∧
        |(mass w φ (ξ (n + 6)) - singularMass) / (mass w φ (ξ (n + 5)) - singularMass)
            - (-Real.exp (-Real.pi / Real.sqrt 7))|
            ≤ (3 / 20 : ℝ) * (21 / 50 : ℝ) ^ n) := by
  sorry
