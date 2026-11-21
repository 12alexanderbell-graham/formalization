import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1A3Certs

/-!
# Proof tools for the third-coefficient bound of matching cubics (B1 at fit level)

Run 2026-11-21T1628Z. The route of `Checked.Trust.NCBN.bn_a3_gen` (run 2026-11-21T1228Z) with the generated cell
certificates of `Checked.Cosmography.B1A3Certs` in place of those of `Checked.Trust.NCBNC`: the three matching
conditions become ratios of distance integrals and polynomial values, the polynomial is written as the displacement
from the point the density implies, and the certificates bound the rescaled displacement of the third coefficient
from below on every density cell of the unit interval.
-/

namespace Checked.Cosmography.B1A3Tools

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1Fit Set

/-- From the third-coefficient bound of `B1A3Certs.a3c_core` back to the paper's coefficient. -/
lemma a3_of (Ω a₃ e₃ : ℝ)
    (he₃ : e₃ = (a₃ / Real.log 10 ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * Real.log 2 ^ 3)
    (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1)
    (h : (491 / 1000 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * (333 / 1000) + 1 / 1000 ≤ e₃) :
    13 / 5 < a₃ := by
  set A := 9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6 with hA
  have hAl : 5 / 18 ≤ A := by nlinarith [sq_nonneg (Ω - 8 / 9)]
  have hℓl := Real.log_two_gt_d9
  have hℓu := Real.log_two_lt_d9
  have c3l : (33302 / 100000 : ℝ) ≤ Real.log 2 ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hℓl.le 3; norm_num at this ⊢; linarith
  have c3u : Real.log 2 ^ 3 ≤ 33303 / 100000 := by
    have := pow_le_pow_left₀ (Real.log_pos (by norm_num)).le hℓu.le 3; norm_num at this ⊢; linarith
  have hl := Checked.Cosmography.B1Fit.log_ten_ge
  norm_num at hl
  have hl0 : 0 < Real.log 10 := by linarith
  have hy491 : 491 / 1000 < a₃ / Real.log 10 ^ 2 := by
    by_contra hc
    rw [not_lt] at hc
    have e1 : e₃ ≤ (491 / 1000 - A) * Real.log 2 ^ 3 := by
      rw [he₃]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : 491 / 1000 - A ≤ 2133 / 10000)
      (by linarith : (0:ℝ) ≤ Real.log 2 ^ 3 - 333 / 1000)]
  have ha : a₃ = a₃ / Real.log 10 ^ 2 * Real.log 10 ^ 2 := by field_simp
  have hl2 : (2302 / 1000 : ℝ) ^ 2 ≤ Real.log 10 ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  rw [ha]
  nlinarith [mul_le_mul_of_nonneg_left hl2 (by linarith : (0:ℝ) ≤ a₃ / Real.log 10 ^ 2)]

theorem a3_bound_gen (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (T t₅ t₃ t₁ t₀ : ℝ) (ht₁ : t₁ ∈ Set.Icc T t₀) (ht₃ : t₃ ∈ Set.Icc T t₀)
    (ht₅ : t₅ ∈ Set.Icc T t₀)
    (hpos : ∀ s ∈ Set.Icc T t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc T t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc T t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅))
    (hm₁ : |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
      ≤ 1 / 20)
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₅ : |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
      ≤ 1 / 20) :
    13 / 5 < a₃ := by
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  -- sources and the bridge to the integral
  have h₁₀ : t₁ ≤ t₀ := ht₁.2
  have h₃₀ : t₃ ≤ t₀ := ht₃.2
  have h₅₀ : t₅ ≤ t₀ := ht₅.2
  have hsub1 : Set.Icc t₁ t₀ ⊆ Set.Icc T t₀ := Set.Icc_subset_Icc_left ht₁.1
  have hsub3 : Set.Icc t₃ t₀ ⊆ Set.Icc T t₀ := Set.Icc_subset_Icc_left ht₃.1
  have hsub5 : Set.Icc t₅ t₀ ⊆ Set.Icc T t₀ := Set.Icc_subset_Icc_left ht₅.1
  have hbr1 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₁ t₀ h₁₀ (fun s hs => hpos s (hsub1 hs))
    (fun s hs => hdiff s (hsub1 hs)) hH₀ (fun s hs => hH s (hsub1 hs))
  have hbr3 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub3 hs))
    (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH s (hsub3 hs))
  have hbr5 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₅ t₀ h₅₀ (fun s hs => hpos s (hsub5 hs))
    (fun s hs => hdiff s (hsub5 hs)) hH₀ (fun s hs => hH s (hsub5 hs))
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨le_trans ht₅.1 h₅₀, le_rfl⟩
  have ha1 : 0 < a t₁ := hpos t₁ ht₁
  have ha3 : 0 < a t₃ := hpos t₃ ht₃
  have ha5 : 0 < a t₅ := hpos t₅ ht₅
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₁ t₀ _ ha1 ha₀ hz₁, es1, hz₁, es1] at hbr1
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hbr3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hbr5
  change lumDistFlat a t₀ t₁ = √2 / hubble a t₀ * ∫ v in √(1 / √2)..1, gL Ω v at hbr1
  change lumDistFlat a t₀ t₃ = 2 * √2 / hubble a t₀ * ∫ v in √(1 / (2 * √2))..1, gL Ω v at hbr3
  change lumDistFlat a t₀ t₅ = 4 * √2 / hubble a t₀ * ∫ v in √(1 / (4 * √2))..1, gL Ω v at hbr5
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v with hJ1
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v with hJ5
  set H₀ := hubble a t₀ with hH₀def
  -- the log-polynomial in u = ln(1+z)
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  set P1 := 1 * ℓ / 2 + a₂ / l * (1 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (1 * ℓ / 2) ^ 3 with hP1def
  set P3 := 3 * ℓ / 2 + a₂ / l * (3 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (3 * ℓ / 2) ^ 3 with hP3def
  set P5 := 5 * ℓ / 2 + a₂ / l * (5 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (5 * ℓ / 2) ^ 3 with hP5def
  have hL1 : logPolyDL3 a₂ a₃ H (redshift a t₀ t₁) = P1 / H := by
    rw [hz₁]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 : logPolyDL3 a₂ a₃ H (redshift a t₀ t₃) = P3 / H := by
    rw [hz₃]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 : logPolyDL3 a₂ a₃ H (redshift a t₀ t₅) = P5 / H := by
    rw [hz₅]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  have hp1' : 0 < P1 := by
    have := hp₁; rw [hL1] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have hp3' : 0 < P3 := by
    have := hp₃; rw [hL3] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have hp5' : 0 < P5 := by
    have := hp₅; rw [hL5] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  -- integral limits
  have hs1 : 1 < √2 := by linarith
  have hs3 : 1 < 2 * √2 := by linarith
  have hs5 : 1 < 4 * √2 := by linarith
  obtain ⟨hw1p, hw1⟩ := w_lt_one _ hs1
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  have hJ1p : 0 < J1 := Jpos Ω _ hΩ₀ hΩ₁ hw1p hw1
  have hJ3p : 0 < J3 := Jpos Ω _ hΩ₀ hΩ₁ hw3p hw3
  have hJ5p : 0 < J5 := Jpos Ω _ hΩ₀ hΩ₁ hw5p hw5
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq2
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have hJ1l : ∫ v in (840897 / 1000000 : ℝ)..1, gL Ω v ≤ J1 :=
    J_shift Ω hΩ₀ hΩ₁ _ _ hw1p wb1l (by norm_num)
  have hJ1u : J1 ≤ ∫ v in (13139 / 15625 : ℝ)..1, gL Ω v :=
    J_shift Ω hΩ₀ hΩ₁ _ _ (by norm_num) wb1u hw1.le
  have hJ3u : J3 ≤ ∫ v in (594603 / 1000000 : ℝ)..1, gL Ω v :=
    J_shift Ω hΩ₀ hΩ₁ _ _ (by norm_num) wb3u hw3.le
  have hJ5l : ∫ v in (420449 / 1000000 : ℝ)..1, gL Ω v ≤ J5 :=
    J_shift Ω hΩ₀ hΩ₁ _ _ hw5p wb5l (by norm_num)
  -- the three matching conditions as distance ratios
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hbr1]; positivity
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hbr3]; positivity
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by rw [hbr5]; positivity
  have r31 : 95499 / 100000 * J1 * P3 ≤ 2 * J3 * P1 := by
    have h := ratio_step _ _ _ _ c hd3 hd1 hp₃ hp₁ hm₃ hm₁
    rw [hbr1, hbr3, hL1, hL3] at h
    exact ratio_clean _ (√2) (2 * √2) H₀ H J1 J3 P3 P1 2 hq2 hH₀ hHp (by ring) h
  have r35 : 95499 / 100000 * J5 * P3 ≤ 1 / 2 * J3 * P5 := by
    have h := ratio_step _ _ _ _ c hd3 hd5 hp₃ hp₅ hm₃ hm₅
    rw [hbr5, hbr3, hL5, hL3] at h
    exact ratio_clean _ (4 * √2) (2 * √2) H₀ H J5 J3 P3 P5 (1 / 2) (by positivity) hH₀ hHp
      (by ring) h
  have r15 : 95499 / 100000 * J5 * P1 ≤ 1 / 4 * J1 * P5 := by
    have h := ratio_step _ _ _ _ c hd1 hd5 hp₁ hp₅ hm₁ hm₅
    rw [hbr5, hbr1, hL5, hL1] at h
    exact ratio_clean _ (4 * √2) (√2) H₀ H J5 J1 P1 P5 (1 / 4) (by positivity) hH₀ hHp
      (by ring) h
  -- displacement from the ΛCDM-implied point, rescaled
  set e₂ := (a₂ / l - (3 / 2 - 3 / 4 * Ω)) * ℓ ^ 2 with he₂
  set e₃ := (a₃ / l ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * ℓ ^ 3 with he₃
  have hP1 : P1 = Qf Ω (1 * ℓ / 2) + 1 / 4 * e₂ + 1 / 8 * e₃ := by
    rw [hP1def, he₂, he₃]; unfold Qf; ring
  have hP3 : P3 = Qf Ω (3 * ℓ / 2) + 9 / 4 * e₂ + 27 / 8 * e₃ := by
    rw [hP3def, he₂, he₃]; unfold Qf; ring
  have hP5 : P5 = Qf Ω (5 * ℓ / 2) + 25 / 4 * e₂ + 125 / 8 * e₃ := by
    rw [hP5def, he₂, he₃]; unfold Qf; ring
  have hcore := Checked.Cosmography.B1A3Certs.a3c_core Ω e₂ e₃ P1 P3 P5 J1 J3 J5 hΩ₀ hΩ₁ hP1 hP3 hP5 hp1' hp3' hp5'
    r31 r35 r15 hJ1l hJ1u hJ3u hJ5l
  exact a3_of Ω a₃ e₃ he₃ hΩ₀ hΩ₁ hcore

end Checked.Cosmography.B1A3Tools
