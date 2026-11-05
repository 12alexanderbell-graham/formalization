import Mathlib
import Work.Data.Moresco16

/-!
# The minimum of the open-ΛCDM χ² of Moresco et al. 2016, certified (THE RESULT part 2)

**Question** (run 2026-11-05T0628Z). Moresco et al. 2016 (arXiv:1601.01701v2) fit the thirty
cosmic-chronometer H(z) values of their Table 4 with the open ΛCDM law (Eq. 5.1) and a Gaussian
prior H₀ = 73 ± 2.4, and print model-comparison numbers (Table 5) built on −2 ln L_max, but not
−2 ln L_max itself. What is the smallest χ² that any parameter values give, to three decimals,
proved over the whole parameter region rather than found by a minimiser?

**What is stated here** (frozen before proof, annex 40.1; definitions `m16Table`, `e2OL`,
`chiSqOL` of `Work.Data.Moresco16`, unchanged):
1. `chiSqOL_ge`: for every H₀ and every (Ω_m, Ω_Λ) with Ω_m ≤ 1, Ω_Λ ≥ 0 and E² ≥ 0 at all
   thirty redshifts (so that the law H₀√E² is real), χ² ≥ 14.9665. The region contains the
   paper's prior region (0 ≤ Ω_m ≤ 1, 0 ≤ z_t ≤ 1.5 with (1 + z_t)³ = 2Ω_Λ/Ω_m).
2. `chiSqOL_lt`: there is a point of the paper's prior region, with E² > 0 at all thirty
   redshifts, where χ² < 14.9675.
3. `chiSqOL_glb_prior`: the greatest lower bound of χ² over the paper's prior region exists and
   lies within 0.0005 of 14.967; `chiSqOL_glb_wide`: the same over the wider region of 1.
4. `table5_oL_aicc_unattainable`: for every N with 4 < N ≤ 31 and every point of the region of 1,
   χ² + 2k + 2k(k + 1)/(N − k − 1) with k = 3 (Eq. 5.4 with −2 ln L = χ²) exceeds the printed
   oΛCDM AICc 21.41 by more than 0.005: no parameter values give the printed number.
-/

namespace Work.Data.Moresco16Min
open Work.Data.Moresco16

/-- For every H₀ and every Ω_m ≤ 1, Ω_Λ ≥ 0 at which E² is nonnegative at all thirty redshifts of
Table 4, the open ΛCDM χ² (with the H₀ prior term) is at least 14.9665. -/
theorem chiSqOL_ge (H0 Ωm ΩΛ : ℝ) (hm : Ωm ≤ 1) (hl : 0 ≤ ΩΛ)
    (hy : ∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) :
    14.9665 ≤ chiSqOL H0 Ωm ΩΛ := by
  sorry

/-- There are H₀, Ω_m, Ω_Λ in the paper's prior region (0 ≤ Ω_m ≤ 1 and 1 ≤ 2Ω_Λ/Ω_m ≤ 15.625,
i.e. 0 ≤ z_t ≤ 1.5) with E² positive at all thirty redshifts of Table 4, at which the open ΛCDM
χ² is below 14.9675. -/
theorem chiSqOL_lt : ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧
    2 * ΩΛ ≤ 15.625 * Ωm ∧ (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧
    chiSqOL H0 Ωm ΩΛ < 14.9675 := by
  sorry

/-- The greatest lower bound of the open ΛCDM χ² over the paper's prior region (every H₀,
0 ≤ Ω_m ≤ 1, Ω_m ≤ 2Ω_Λ ≤ 15.625 Ω_m, E² positive at all thirty redshifts) exists and is
within 0.0005 of 14.967. -/
theorem chiSqOL_glb_prior : ∃ m : ℝ,
    IsGLB {x | ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧ 2 * ΩΛ ≤ 15.625 * Ωm ∧
      (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} m ∧
    |m - 14.967| ≤ 0.0005 := by
  sorry

/-- The greatest lower bound of the open ΛCDM χ² over every H₀ and every Ω_m ≤ 1, Ω_Λ ≥ 0 with E²
nonnegative at all thirty redshifts exists and is within 0.0005 of 14.967. -/
theorem chiSqOL_glb_wide : ∃ m : ℝ,
    IsGLB {x | ∃ H0 Ωm ΩΛ : ℝ, Ωm ≤ 1 ∧ 0 ≤ ΩΛ ∧
      (∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} m ∧
    |m - 14.967| ≤ 0.0005 := by
  sorry

/-- Table 5, oΛCDM row: for every N with 4 < N ≤ 31 and every H₀, Ω_m ≤ 1, Ω_Λ ≥ 0 with E²
nonnegative at all thirty redshifts, the AICc of Eq. 5.4 computed with −2 ln L = χ² and k = 3
exceeds the printed 21.41 by more than 0.005. -/
theorem table5_oL_aicc_unattainable (N H0 Ωm ΩΛ : ℝ) (hN : 4 < N) (hN31 : N ≤ 31)
    (hm : Ωm ≤ 1) (hl : 0 ≤ ΩΛ) (hy : ∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) :
    21.41 + 0.005 < chiSqOL H0 Ωm ΩΛ + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) := by
  sorry

end Work.Data.Moresco16Min
