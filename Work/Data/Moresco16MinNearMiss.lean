import Mathlib
import Work.Data.Moresco16Min

/-!
# Near misses of the certified χ² minimum (audit, run 2026-11-05T0628Z)

Statement-level checks that the frozen headlines of `Work.Data.Moresco16Min` bite:
* `near_miss_bound`: raising the lower bound of `chiSqOL_ge` from 14.9665 to 14.9675 makes it
  false (the bound is within 0.001 of the minimum).
* `aic_reading_attainable`: claim 4 (`table5_oL_aicc_unattainable`) depends on reading the printed
  column as the AICc of Eq. 5.4: under the plain AIC of Eq. 5.3 (k = 3, −2 ln L = χ²) the printed
  21.41 is attained exactly at a point of the paper's prior region (the referee's alternative
  reading, `runs/2026-11-05T0628Z/referee_min.md`).
-/

namespace Work.Data.Moresco16MinNearMiss
open Work.Data.Moresco16 Work.Data.Moresco16Min

/-- The lower bound 14.9665 of `chiSqOL_ge` cannot be raised to 14.9675. -/
theorem near_miss_bound : ¬ ∀ H0 Ωm ΩΛ : ℝ, Ωm ≤ 1 → 0 ≤ ΩΛ →
    (∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) → 14.9675 ≤ chiSqOL H0 Ωm ΩΛ := by
  intro h
  obtain ⟨H1, m1, l1, a1, a2, a3, a4, a5, a6⟩ := chiSqOL_lt
  have := h H1 m1 l1 a2 (by linarith) fun i => (a5 i).le
  linarith

theorem continuous_chiSqOL (Ωm ΩΛ : ℝ) : Continuous fun H0 => chiSqOL H0 Ωm ΩΛ := by
  unfold chiSqOL
  fun_prop

/-- Under the plain AIC of Eq. 5.3 (k = 3, −2 ln L = χ²), the printed oΛCDM value 21.41 is attained
at a point of the paper's prior region with E² positive at all thirty redshifts. -/
theorem aic_reading_attainable : ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧
    2 * ΩΛ ≤ 15.625 * Ωm ∧ (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧
    chiSqOL H0 Ωm ΩΛ + 2 * 3 = 21.41 := by
  obtain ⟨H1, m1, l1, a1, a2, a3, a4, a5, a6⟩ := chiSqOL_lt
  set f := fun H0 => chiSqOL H0 m1 l1 with hf
  have hprior : ∀ H0, (H0 - 73) ^ 2 / 2.4 ^ 2 ≤ f H0 := by
    intro H0
    simp only [hf]
    unfold chiSqOL
    have hs : 0 ≤ ∑ i, (H0 * Real.sqrt (e2OL m1 l1 (m16Table i).1) - (m16Table i).2.1) ^ 2 /
        (m16Table i).2.2 ^ 2 := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hH1 : H1 ≤ 200 := by
    have h1 := hprior H1
    have h2 : f H1 < 14.9675 := a6
    have h3 : (H1 - 73) ^ 2 < 14.9675 * 2.4 ^ 2 := by
      have := lt_of_le_of_lt h1 h2
      rwa [div_lt_iff₀ (by norm_num)] at this
    nlinarith
  have hbig : 15.41 ≤ f 200 := by
    have := hprior 200
    norm_num at this
    linarith
  obtain ⟨H, hH, hfH⟩ := intermediate_value_Icc hH1
    (continuous_chiSqOL m1 l1).continuousOn ⟨by linarith, hbig⟩
  exact ⟨H, m1, l1, a1, a2, a3, a4, a5, by simp only at hfH; rw [hfH]; norm_num⟩

end Work.Data.Moresco16MinNearMiss

#print axioms Work.Data.Moresco16MinNearMiss.near_miss_bound
#print axioms Work.Data.Moresco16MinNearMiss.aic_reading_attainable
