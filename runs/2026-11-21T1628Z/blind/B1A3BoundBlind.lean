import Checked.Cosmography.B1Truncation

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- Distance modulus (up to the usual additive constant) of a luminosity distance `d`. -/
noncomputable def blindModulus (d : ℝ) : ℝ := 5 * Real.logb 10 d

/-- Cubic log-polynomial fit `logPolyDL3` reproduces the flat universe `a`'s distance
modulus within `0.05` mag at the three sources `t₁ t₂ t₃` (seen from `t₀`), up to one
common offset `Δ`. -/
theorem blind_a3_bound
    (a : ℝ → ℝ) (t₀ t₁ t₂ t₃ : ℝ) (H₀ Ωm : ℝ)
    -- ΛCDM data
    (hH₀ : 0 < H₀) (hΩ : Ωm ∈ Set.Icc (0 : ℝ) 1)
    -- sources are in the past, earliest (largest redshift) is `t₃`
    (h32 : t₃ < t₂) (h21 : t₂ < t₁) (h10 : t₁ < t₀)
    -- scale factor is positive and differentiable on the relevant epoch `[t₃, t₀]`
    (hpos : ∀ t ∈ Set.Icc t₃ t₀, 0 < a t)
    (hdiff : ∀ t ∈ Set.Icc t₃ t₀, DifferentiableAt ℝ a t)
    -- exact flat ΛCDM expansion law on the relevant epoch, with `1 + z = a t₀ / a t`
    (hlaw : ∀ t ∈ Set.Icc t₃ t₀,
      hubble a t = H₀ * Real.sqrt (Ωm * (1 + redshift a t₀ t) ^ 3 + 1 - Ωm))
    -- the three sources
    (hz1 : 1 + redshift a t₀ t₁ = Real.sqrt 2)
    (hz2 : 1 + redshift a t₀ t₂ = 2 * Real.sqrt 2)
    (hz3 : 1 + redshift a t₀ t₃ = 4 * Real.sqrt 2)
    -- cubic log-polynomial fit, any `a₂ a₃`, any `H > 0`
    (a₂ a₃ H : ℝ) (hH : 0 < H)
    -- fit is positive at the three redshifts
    (hp1 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp2 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₂))
    (hp3 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    -- within 0.05 mag at all three redshifts, up to one common magnitude offset
    (hfit : ∃ Δ : ℝ,
      |blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
          - blindModulus (lumDistFlat a t₀ t₁) - Δ| ≤ 0.05 ∧
      |blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₂))
          - blindModulus (lumDistFlat a t₀ t₂) - Δ| ≤ 0.05 ∧
      |blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
          - blindModulus (lumDistFlat a t₀ t₃) - Δ| ≤ 0.05) :
    a₃ > 13 / 5 := by
  sorry
