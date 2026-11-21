import Checked.Cosmography.B1A3Bound
import Checked.Trust.NecessityAP
import Checked.Trust.NecessityL
import Checked.Trust.NecessityBL
import Checked.Trust.NecessityAR

/-!
# Hypothesis necessity, the third-coefficient headline of the B1 fit (trust track T2b)

Run 2026-11-21T1628Z. `B1A3Bound.third_coefficient_lower_bound` has the hypotheses of `B1Fit.fit_direction` with a
different conclusion. Six of the redundancy proofs of the direction do not use its conclusion: they derive the
dropped hypothesis from the others (positivity of the scale factor up to a sign, differentiability and the sign of
the present rate from the expansion law), or show that without it the remaining hypotheses contradict each other
(the normalisation and the positivity of the polynomial at the nearest and the farthest source). They are copied
here with the new headline in place of the direction.

Seven needed witnesses of the direction carry over with a cubic whose third coefficient is below the bound: the
three time orders (a scale factor of the program's witness family whose distances vanish, so every residual
condition holds with offset zero; the third coefficient set to zero), the two redshift placements and the two
residual conditions at the middle and the farthest source (the Einstein–de Sitter model with cubics whose third
coefficient is negative). Their certified residual bands are those of the direction's witnesses.
-/

namespace Checked.Trust.NCBO

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1Fit Set
open Checked.Trust.NCAP Checked.Trust.NCL Checked.Trust.NCBL Checked.Trust.NCBI Checked.Trust.NCAR Checked.Trust.NCAQ

theorem third_coefficient_lower_bound_r6 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 6 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans (h31.trans h10)) hdiff hH₀ hH with hp | hn
  · exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hp hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  · exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 (fun x => -a x) t₅ t₃ t₁ t₀ h53 h31 h10
      (pos_neg a t₅ t₀ hn) (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₅ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) (by rwa [redshift_neg]) a₂ a₃ H c hHp
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) (by rwa [redshift_neg])
      (by rwa [redshift_neg, lumDistFlat_neg]) (by rwa [redshift_neg, lumDistFlat_neg])
      (by rwa [redshift_neg, lumDistFlat_neg])

theorem third_coefficient_lower_bound_r7 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 7 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5

theorem third_coefficient_lower_bound_r8 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 8 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 (le_trans h31 h10)) hpos hdiff hH (hz5 ▸ z5_pos))
    hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5

theorem third_coefficient_lower_bound_r13 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 13 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hp1 hp3 hp5
    hm1 hm3 hm5
  rcases lt_or_ge 0 H with hHp | hHn
  · exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  exfalso
  rcases eq_or_lt_of_le hHn with hH0 | hHn
  · rw [hH0] at hp1; unfold logPolyDL3 at hp1; simp at hp1
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb1 := bl_bridge Ω h0 h1 a t₅ t₁ t₀ (h53.trans h31) h10 hpos hdiff hH₀ hH (√2) hz1
  have hb3 := bl_bridge Ω h0 h1 a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  have hb5 := bl_bridge Ω h0 h1 a t₅ t₅ t₀ le_rfl (h53.trans (h31.trans h10)) hpos hdiff hH₀ hH
    (4 * √2) hz5
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hb1]; exact bl_pos Ω h0 h1 _ hw1p hw11 _ _ hq hH₀
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hb3]; exact bl_pos Ω h0 h1 _ hw3p hw31 _ _ (by positivity) hH₀
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by rw [hb5]; exact bl_pos Ω h0 h1 _ hw5p hw51 _ _ (by positivity) hH₀
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHn.ne hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHn.ne hu3
  have hL5 := lp_eq a₂ a₃ H _ _ hHn.ne hu5
  have hrel := bl_rel a₂ a₃
  set P1 := 1 * ℓ / 2 + a₂ / Real.log 10 * (1 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (1 * ℓ / 2) ^ 3
  set P3 := 3 * ℓ / 2 + a₂ / Real.log 10 * (3 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (3 * ℓ / 2) ^ 3
  set P5 := 5 * ℓ / 2 + a₂ / Real.log 10 * (5 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (5 * ℓ / 2) ^ 3
  have hN : ∀ P : ℝ, P / H = -P / -H := fun P => (neg_div_neg_eq P H).symm
  have hHm : 0 < -H := by linarith
  have hQ3 : 0 < -P3 := by
    have := hp3; rw [hz3, hL3, hN] at this; exact (div_pos_iff_of_pos_right hHm).1 this
  have ha := ratio_step _ _ _ _ c hd3 hd1 hp3 hp1 hm3 hm1
  rw [hb1, hb3, hz1, hz3, hL1, hL3, hN P1, hN P3] at ha
  have hc := ratio_step _ _ _ _ c hd3 hd5 hp3 hp5 hm3 hm5
  rw [hb5, hb3, hz5, hz3, hL5, hL3, hN P5, hN P3] at hc
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v
  have r13 := ratio_clean _ (√2) (2 * √2) _ (-H) J1 J3 (-P3) (-P1) 2 hq hH₀ hHm (by ring) ha
  have r53 := ratio_clean _ (4 * √2) (2 * √2) _ (-H) J5 J3 (-P3) (-P5) (1 / 2) (by positivity) hH₀ hHm
    (by ring) hc
  have hJ3 : 0 < J3 := Jpos Ω _ h0 h1 hw3p hw31
  have hcomb := bl_comb Ω h0 h1
  -- κ Q₃ (15 J₁ + 12/5 J₅) ≤ J₃ (30 Q₁ + 6/5 Q₅) < 20/3 J₃ Q₃ ≤ κ Q₃ (15 J₁ + 12/5 J₅)
  have h1' : J3 * (30 * -P1 + 6 / 5 * -P5) < J3 * (20 / 3 * -P3) :=
    mul_lt_mul_of_pos_left (by linarith only [hrel, hℓ0]) hJ3
  have h2' : 20 / 3 * J3 * -P3 ≤
      95499 / 100000 * (15 * J1 + 12 / 5 * J5) * -P3 := mul_le_mul_of_nonneg_right hcomb hQ3.le
  linarith only [h1', h2', r13, r53]

theorem third_coefficient_lower_bound_r14 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 14 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp3 hp5
    hm1 hm3 hm5
  rcases lt_or_ge 0 (logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) with hp1 | hp1
  · exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  exfalso
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb3 := bl_bridge Ω h0 h1 a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  have hb5 := bl_bridge Ω h0 h1 a t₅ t₅ t₀ le_rfl (h53.trans (h31.trans h10)) hpos hdiff hH₀ hH
    (4 * √2) hz5
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hb3]; exact bl_pos Ω h0 h1 _ hw3p hw31 _ _ (by positivity) hH₀
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by rw [hb5]; exact bl_pos Ω h0 h1 _ hw5p hw51 _ _ (by positivity) hH₀
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 := lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  rw [hz1, hL1] at hp1
  have hrel := bl_rel a₂ a₃
  set P1 := 1 * ℓ / 2 + a₂ / Real.log 10 * (1 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (1 * ℓ / 2) ^ 3
  set P3 := 3 * ℓ / 2 + a₂ / Real.log 10 * (3 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (3 * ℓ / 2) ^ 3
  set P5 := 5 * ℓ / 2 + a₂ / Real.log 10 * (5 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (5 * ℓ / 2) ^ 3
  have hP1 : P1 ≤ 0 := by
    by_contra hc; push Not at hc; have := div_pos hc hHp; linarith
  have hP3 : 0 < P3 := by
    have := hp3; rw [hz3, hL3] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have h := ratio_step _ _ _ _ c hd5 hd3 hp5 hp3 hm5 hm3
  rw [hb3, hb5, hz3, hz5, hL3, hL5] at h
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v
  have r := ratio_clean _ (2 * √2) (4 * √2) _ H J3 J5 P5 P3 2 (by positivity) hH₀ hHp (by ring) h
  have hJ3 : 0 < J3 := Jpos Ω _ h0 h1 hw3p hw31
  have hρ := bl_ratio53 Ω h0 h1
  -- κ J₃ P₅ ≤ 2 J₅ P₃ ≤ 2 ρ J₃ P₃ with ρ = (4√2 − 1)/(2√2 − 1) < 2.55, while P₅ > 50/9 P₃
  have hJ5 : (2 * √2 - 1) * J5 ≤ (4 * √2 - 1) * J3 := hρ
  have h2 : (2 * √2 - 1) * (95499 / 100000 * J3 * P5) ≤ 2 * (4 * √2 - 1) * J3 * P3 := by
    have hA0 : (0:ℝ) ≤ 2 * √2 - 1 := by linarith
    linarith only [mul_le_mul_of_nonneg_left r hA0,
      mul_le_mul_of_nonneg_right hJ5 (by linarith : (0:ℝ) ≤ 2 * P3)]
  have h3 : 6 / 5 * P5 > 20 / 3 * P3 := by linarith
  have h4 : (2 * √2 - 1) * (95499 / 100000) * P5 ≤ 2 * (4 * √2 - 1) * P3 := by
    have := h2; rw [show (2 * √2 - 1) * (95499 / 100000 * J3 * P5) = J3 * ((2 * √2 - 1) * (95499 / 100000) * P5)
      by ring, show 2 * (4 * √2 - 1) * J3 * P3 = J3 * (2 * (4 * √2 - 1) * P3) by ring] at this
    exact le_of_mul_le_mul_left this hJ3
  have hA : 0 < (2 * √2 - 1) * (95499 / 100000) := by
    have : (0:ℝ) < 2 * √2 - 1 := by linarith only [hq2l]
    positivity
  have h5 : (2 * √2 - 1) * (95499 / 100000) * (50 / 9 * P3) < (2 * √2 - 1) * (95499 / 100000) * P5 :=
    mul_lt_mul_of_pos_left (by linarith only [h3]) hA
  have h6 : 0 < ((2 * √2 - 1) * (95499 / 100000) * (50 / 9) - 2 * (4 * √2 - 1)) * P3 :=
    mul_pos (by linarith only [hq2l, hq2u]) hP3
  linarith only [h4, h5, h6]

theorem third_coefficient_lower_bound_r16 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 16 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3
    hm1 hm3 hm5
  rcases lt_or_ge 0 (logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) with hp5 | hp5
  · exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  exfalso
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb1 := bl_bridge Ω h0 h1 a t₅ t₁ t₀ (h53.trans h31) h10 hpos hdiff hH₀ hH (√2) hz1
  have hb3 := bl_bridge Ω h0 h1 a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hb1]; exact bl_pos Ω h0 h1 _ hw1p hw11 _ _ hq hH₀
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hb3]; exact bl_pos Ω h0 h1 _ hw3p hw31 _ _ (by positivity) hH₀
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 := lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  rw [hz5, hL5] at hp5
  have hrel := bl_rel a₂ a₃
  set P1 := 1 * ℓ / 2 + a₂ / Real.log 10 * (1 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (1 * ℓ / 2) ^ 3
  set P3 := 3 * ℓ / 2 + a₂ / Real.log 10 * (3 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (3 * ℓ / 2) ^ 3
  set P5 := 5 * ℓ / 2 + a₂ / Real.log 10 * (5 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (5 * ℓ / 2) ^ 3
  have hP5 : P5 ≤ 0 := by
    by_contra hc; push Not at hc; have := div_pos hc hHp; linarith
  have hP3 : 0 < P3 := by
    have := hp3; rw [hz3, hL3] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have h := ratio_step _ _ _ _ c hd1 hd3 hp1 hp3 hm1 hm3
  rw [hb1, hb3, hz1, hz3, hL1, hL3] at h
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  have r := ratio_clean _ (2 * √2) (√2) _ H J3 J1 P1 P3 (1 / 2) (by positivity) hH₀ hHp (by ring) h
  have hJ3 : 0 < J3 := Jpos Ω _ h0 h1 hw3p hw31
  have hσ := bl_ratio13 Ω h0 h1
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  -- κ J₃ P₁ ≤ J₁ P₃ / 2 ≤ σ J₃ P₃ / 2 with σ = (1 − w₁)/(1 − w₃) < 0.393, while P₁ > 2/9 P₃
  have hJ1 : (1 - √(1 / (2 * √2))) * J1 ≤ (1 - 13139 / 15625) * J3 := by
    have : (1 - √(1 / √2)) * J3 ≤ (1 - 13139 / 15625) * J3 :=
      mul_le_mul_of_nonneg_right (by linarith) hJ3.le
    linarith
  have hA : 0 < 1 - √(1 / (2 * √2)) := by linarith
  have h2 : (1 - √(1 / (2 * √2))) * (95499 / 100000 * J3 * P1) ≤ 1 / 2 * (1 - 13139 / 15625) * J3 * P3 := by
    linarith only [mul_le_mul_of_nonneg_right hJ1 (by linarith : (0:ℝ) ≤ 1 / 2 * P3),
      mul_le_mul_of_nonneg_left r hA.le]
  have h4 : (1 - √(1 / (2 * √2))) * (95499 / 100000) * P1 ≤ 1 / 2 * (1 - 13139 / 15625) * P3 := by
    have := h2; rw [show (1 - √(1 / (2 * √2))) * (95499 / 100000 * J3 * P1)
        = J3 * ((1 - √(1 / (2 * √2))) * (95499 / 100000) * P1) by ring,
      show 1 / 2 * (1 - 13139 / 15625) * J3 * P3 = J3 * (1 / 2 * (1 - 13139 / 15625) * P3) by ring] at this
    exact le_of_mul_le_mul_left this hJ3
  have h3 : 30 * P1 > 20 / 3 * P3 := by linarith
  have hP1 : 0 < P1 := by linarith
  have h5 : (148651 / 250000 : ℝ) ≥ √(1 / (2 * √2)) := wb3l
  have h6 : (1 - 148651 / 250000) * (95499 / 100000) * P1 ≤ (1 - √(1 / (2 * √2))) * (95499 / 100000) * P1 := by
    apply mul_le_mul_of_nonneg_right _ hP1.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith
  linarith only [h4, h6, h3, hP3]

theorem third_coefficient_lower_bound_h3 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-2, 1 / (1 + (2 * √2 - 1))),
    (-1, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (-1) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (-2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (-2) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, -2, -1, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, lusA2 (1 / 5), 0, 1, 0, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num, ?_⟩
  norm_num

theorem third_coefficient_lower_bound_h4 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1))),
    (-1, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (-1) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, -1, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, lusA2 (1 / 5), 0, 1, 0, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num, ?_⟩
  norm_num

theorem third_coefficient_lower_bound_h5 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 5 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1))),
    (3, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (3) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (3) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, 3, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, lusA2 (1 / 5), 0, 1, 0, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ lusA2_pos le_rfl one_pos (by linarith),
    by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num, ?_⟩
  norm_num

theorem third_coefficient_lower_bound_h11 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 11 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, tE √2, tE √2, 1, le_trans o53 o31, le_rfl, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S5.1,
    (171 / 4 : ℝ), (-23:ℝ), 3.5495, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_1.1 (by norm_num) (by norm_num)
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_1.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_5.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_1.1 B_fit18_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_1.1 B_fit18_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_5.1 B_fit18_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num

theorem third_coefficient_lower_bound_h12 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 12 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p3
  refine ⟨1, by norm_num, le_rfl, ea, tE (2 * √2), tE (2 * √2), _, 1, le_rfl, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1,
    (8:ℝ), (-21 / 4 : ℝ), 1.0706, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_3.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_3.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_1.1 B_fit19_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_3.1 B_fit19_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_3.1 B_fit19_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num

theorem third_coefficient_lower_bound_h18 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 18 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (171 / 4 : ℝ), (-23:ℝ), 3.5495, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_5.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_1.1 B_fit18_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_5.1 B_fit18_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num

theorem third_coefficient_lower_bound_h19 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 19 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (8:ℝ), (-21 / 4 : ℝ), 1.0706, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_5.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_1.1 B_fit19_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_3.1 B_fit19_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num

end Checked.Trust.NCBO
