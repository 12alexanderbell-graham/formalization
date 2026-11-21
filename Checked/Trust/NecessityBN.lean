import Checked.Trust.NecessityBI
import Checked.Cosmography.B1FitRL19

/-!
# Hypothesis necessity, the fit-direction headline and its RL19 corollary: the lower density bound and three box bounds (trust track T2b)

Run 2026-11-21T1228Z. `B1Fit.fit_direction` and `B1FitRL19.rl19_box_unmatched` assume a matter density between
zero and one. Their first hypothesis `0 ≤ Ω` is REDUNDANT in both: the conclusions hold for every negative density
the expansion law admits, with no certified integral.

* **Too negative a density cannot reach the farthest source** (`NCBI.bi_unreach`): at or below minus one in one
  hundred and eighty the radicand `Ω(1+z)³ + 1 − Ω` is negative at the farthest source.
* **Nearest source** (`bn_near`): above that density and below zero, the change of variables (`NCBI.bi_bridge`)
  and the comparison with the empty model above the source (`NCBI.bi_upper`) bound the distance by the empty
  model's times a factor of at most one and one hundredth, so by forty-two hundredths of `√2 / H₀`.
* **Farthest source** (`bn_far`): a time where the scale factor is two elevenths of its present value lies
  between the middle and the farthest source (intermediate value); from it the comoving distance to the
  farthest source is at least the empty model's from that time (`NCBI.bi_lower` with the comparison point at
  the present), so the distance is at least four and a half times `4√2 / H₀`.
* **The conclusion** (`fit_direction_r1`): the residuals at the nearest and the farthest source then bound the
  rescaled polynomial value at the nearest source by a small multiple of the one at the farthest, and with the
  middle value positive this alone puts the rescaled combination of the conclusion above three and a half,
  where `B1Fit.conclude` needs about one tenth.
* **The RL19 corollary** (`rl19_box_unmatched_r1`): its proof is the direction plus a quadratic inequality on the
  box that holds for every density up to one (`bn_box_neg`), so the first statement without its lower bound
  carries it over.
* **Two box bounds of the RL19 corollary** (`rl19_box_unmatched_r14`, `rl19_box_unmatched_r15`): the direction
  functional decreases in `a₂` and increases in `a₃`, so the upper bound on `a₂` and the lower bound on `a₃` are
  REDUNDANT.
* **The upper bound on `a₃` is NEEDED** (`rl19_box_unmatched_h16`): at density one fifth (the exact model of
  `B1FitWitness.exists_model` and its enclosures of the three distance integrals) a cubic at the lower corner of
  the box in `a₂` with a larger `a₃` matches all three distance moduli within a twentieth of a magnitude.
-/

namespace Checked.Trust.NCBN

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1Fit Set
open Checked.Trust.NCBI

/-- Nearest source, density in `(−1/180, 0]`: the distance is positive and at most `√2 · 21/50 / H₀`. -/
theorem bn_near (Ω : ℝ) (hlo : -1 / 180 < Ω) (hΩ : Ω ≤ 0)
    (a : ℝ → ℝ) (t₁ t₀ : ℝ) (h₁₀ : t₁ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₁ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₁ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₁ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) :
    0 < lumDistFlat a t₀ t₁ ∧ lumDistFlat a t₀ t₁ ≤ √2 * (21 / 50) / hubble a t₀ := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2s : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : 0 < √2 := by linarith
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₁₀, le_rfl⟩
  have ha1 : 0 < a t₁ := hpos t₁ ⟨le_rfl, h₁₀⟩
  have hr1 := ratio_of_z a t₁ t₀ _ ha1 ha₀ hz₁
  rw [show (1:ℝ) + (√2 - 1) = √2 by ring] at hr1
  have hw2 : √(a t₁ / a t₀) ^ 2 = 1 / √2 := by rw [Real.sq_sqrt (div_pos ha1 ha₀).le, hr1]
  have hw0 : 0 < √(a t₁ / a t₀) := Real.sqrt_pos.2 (div_pos ha1 ha₀)
  have hw1 : √(a t₁ / a t₀) ≤ 1 := by
    rw [Real.sqrt_le_one, hr1, div_le_one hq]; linarith
  have hw6 : √(a t₁ / a t₀) ^ 6 = 1 / (2 * √2) := by
    rw [show √(a t₁ / a t₀) ^ 6 = (√(a t₁ / a t₀) ^ 2) ^ 3 by ring, hw2, div_pow, one_pow,
      show √2 ^ 3 = √2 ^ 2 * √2 by ring, hq2s]
  have hw6l : (3535 / 10000 : ℝ) ≤ √(a t₁ / a t₀) ^ 6 := by
    rw [hw6, le_div_iff₀ (by positivity)]; nlinarith
  have hw6u : √(a t₁ / a t₀) ^ 6 ≤ 3536 / 10000 := by
    rw [hw6, div_le_iff₀ (by positivity)]; nlinarith
  have hR : 0 < Ω + (1 - Ω) * √(a t₁ / a t₀) ^ 6 := by nlinarith
  have hb := bi_bridge Ω (by linarith) a t₁ t₀ h₁₀ hpos hdiff hH₀ hH hR
  rw [hz₁, show (1:ℝ) + (√2 - 1) = √2 by ring] at hb
  set w := √(a t₁ / a t₀) with hwdef
  have hup := bi_upper Ω w hΩ hw0 hw1 hR
  have hlow := bi_lower Ω w 1 hΩ hw0 hw1 hR
  have e1 : (1:ℝ) ^ 3 / √(Ω + (1 - Ω) * 1 ^ 6) = 1 := by
    rw [show Ω + (1 - Ω) * (1:ℝ) ^ 6 = 1 by ring]; simp
  have hiw : 1 / w ^ 2 = √2 := by rw [hw2]; field_simp
  rw [e1, hiw, show (1:ℝ) / 1 ^ 2 = 1 by norm_num] at hlow
  rw [hiw, show (1:ℝ) / 1 ^ 2 = 1 by norm_num] at hup
  have hr : w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) ≤ 101 / 100 := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hR)]
    have e : (101 / 100 : ℝ) * √(Ω + (1 - Ω) * w ^ 6) = √((101 / 100) ^ 2 * (Ω + (1 - Ω) * w ^ 6)) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [e]
    apply Real.le_sqrt_of_sq_le
    rw [show (w ^ 3) ^ 2 = w ^ 6 by ring]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Ω + 1 / 180) (by linarith : (0:ℝ) ≤ 1 - w ^ 6)]
  have hJu : (∫ v in w..1, 2 / √(Ω + (1 - Ω) * v ^ 6)) ≤ 101 / 100 * (√2 - 1) :=
    le_trans hup (mul_le_mul_of_nonneg_right hr (by linarith))
  have hJl : 0 < ∫ v in w..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
    have : (0:ℝ) < 1 * (√2 - 1) := by linarith
    linarith
  rw [hb]
  refine ⟨by positivity, ?_⟩
  rw [show √2 * (21 / 50) / hubble a t₀ = √2 / hubble a t₀ * (21 / 50) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- Farthest source, density in `(−1/180, 0]`: the distance is at least `4√2 · 9/2 / H₀`. -/
theorem bn_far (Ω : ℝ) (hlo : -1 / 180 < Ω) (hΩ : Ω ≤ 0)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1) :
    4 * √2 * (9 / 2) / hubble a t₀ ≤ lumDistFlat a t₀ t₅ := by
  have h₅₀ : t₅ ≤ t₀ := le_trans h₅₃ h₃₀
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₅₃, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hr3 := ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃
  have hr5 := ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅
  rw [show (1:ℝ) + (2 * √2 - 1) = 2 * √2 by ring] at hr3
  rw [show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring] at hr5
  have hsub : ∀ u, t₅ ≤ u → Set.Icc u t₀ ⊆ Set.Icc t₅ t₀ := fun u hu => Set.Icc_subset_Icc_left hu
  have hcont : ContinuousOn a (Set.Icc t₅ t₃) := fun x hx =>
    (hdiff x ⟨hx.1, le_trans hx.2 h₃₀⟩).continuousAt.continuousWithinAt
  have e5 : a t₅ = a t₀ / (4 * √2) := by
    field_simp at hr5 ⊢; linarith
  have e3 : a t₃ = a t₀ / (2 * √2) := by
    field_simp at hr3 ⊢; linarith
  have hin : a t₀ * (2 / 11) ∈ Set.Icc (a t₅) (a t₃) := by
    rw [e5, e3]
    constructor
    · rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hq2l ha₀.le]
    · rw [le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hq2u ha₀.le]
  obtain ⟨s, hs, has⟩ := intermediate_value_Icc h₅₃ hcont hin
  have hs₀ : s ≤ t₀ := le_trans hs.2 h₃₀
  have has0 : a s / a t₀ = 2 / 11 := by rw [has]; field_simp
  have hp0 : 0 < √(2 / 11 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hp2 : √(2 / 11 : ℝ) ^ 2 = 2 / 11 := Real.sq_sqrt (by norm_num)
  have hp1 : √(2 / 11 : ℝ) ≤ 1 := by rw [Real.sqrt_le_one]; norm_num
  have hp6 : √(2 / 11 : ℝ) ^ 6 = 8 / 1331 := by
    rw [show √(2 / 11 : ℝ) ^ 6 = (√(2 / 11 : ℝ) ^ 2) ^ 3 by ring, hp2]; norm_num
  have hR : 0 < Ω + (1 - Ω) * √(2 / 11 : ℝ) ^ 6 := by rw [hp6]; linarith
  have hsp : √(a s / a t₀) = √(2 / 11 : ℝ) := by rw [has0]
  have hbs := bi_bridge Ω (by linarith) a s t₀ hs₀ (fun u hu => hpos u (hsub s hs.1 hu))
    (fun u hu => hdiff u (hsub s hs.1 hu)) hH₀ (fun u hu => hH u (hsub s hs.1 hu))
    (by rw [hsp]; exact hR)
  rw [hsp] at hbs
  have hzs : 1 + redshift a t₀ s = 11 / 2 := by
    unfold redshift; rw [has]; field_simp; ring
  rw [hzs] at hbs
  have hlow := bi_lower Ω (√(2 / 11 : ℝ)) 1 hΩ hp0 hp1 hR
  have e1 : (1:ℝ) ^ 3 / √(Ω + (1 - Ω) * 1 ^ 6) = 1 := by
    rw [show Ω + (1 - Ω) * (1:ℝ) ^ 6 = 1 by ring]; simp
  rw [e1, hp2] at hlow
  have hJ : 9 / 2 ≤ ∫ v in √(2 / 11 : ℝ)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
    have : (1:ℝ) * (1 / (2 / 11) - 1 / 1 ^ 2) = 9 / 2 := by norm_num
    linarith
  have hcom : comoving a t₀ s ≤ comoving a t₀ t₅ := by
    unfold comoving
    have hc : ContinuousOn (fun u => 1 / a u) (Set.Icc t₅ t₀) := fun x hx =>
      (continuousAt_const.div (hdiff x hx).continuousAt (hpos x hx).ne').continuousWithinAt
    have hi1 : IntervalIntegrable (fun u => 1 / a u) MeasureTheory.volume t₅ s :=
      (hc.mono (Set.Icc_subset_Icc_right hs₀)).intervalIntegrable_of_Icc hs.1
    have hi2 : IntervalIntegrable (fun u => 1 / a u) MeasureTheory.volume s t₀ :=
      (hc.mono (hsub s hs.1)).intervalIntegrable_of_Icc hs₀
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have : 0 ≤ ∫ u in t₅..s, 1 / a u :=
      intervalIntegral.integral_nonneg hs.1 (fun u hu =>
        (div_pos one_pos (hpos u ⟨hu.1, le_trans hu.2 hs₀⟩)).le)
    linarith
  have hD5 : 4 * √2 * (2 / 11) * lumDistFlat a t₀ s ≤ lumDistFlat a t₀ t₅ := by
    unfold lumDistFlat
    rw [hzs, hz₅, show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring]
    calc 4 * √2 * (2 / 11) * (a t₀ * (11 / 2) * comoving a t₀ s)
        = a t₀ * (4 * √2) * comoving a t₀ s := by ring
      _ ≤ a t₀ * (4 * √2) * comoving a t₀ t₅ := mul_le_mul_of_nonneg_left hcom (by positivity)
  rw [hbs] at hD5
  have hH0p := hH₀
  calc 4 * √2 * (9 / 2) / hubble a t₀
      = 4 * √2 * (2 / 11) * (11 / 2 / hubble a t₀ * (9 / 2)) := by field_simp
    _ ≤ 4 * √2 * (2 / 11) * (11 / 2 / hubble a t₀ *
          ∫ v in √(2 / 11 : ℝ)..1, 2 / √(Ω + (1 - Ω) * v ^ 6)) := by gcongr
    _ ≤ _ := hD5

/-- Without `0 ≤ Ω`: a density at or below `−1/180` cannot reach the farthest source (`bi_unreach`); above it the
residuals at the nearest and the farthest source alone give the direction (`bn_near`, `bn_far`). -/
theorem fit_direction_r1 : dropped% Checked.Cosmography.B1Fit.fit_direction 1 := by
  intro Ω h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  rcases le_or_gt 0 Ω with h0 | hneg
  · exact Checked.Cosmography.B1Fit.fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2s : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : 0 < √2 := by linarith
  have h50 : t₅ ≤ t₀ := h53.trans (h31.trans h10)
  rcases lt_or_ge (-1 / 180) Ω with hlo | hc
  swap
  · exfalso
    apply bi_unreach Ω a t₅ t₀ h50 hpos hdiff hH
    rw [hz5, show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring]
    have e : (4 * √2) ^ 3 = 128 * √2 := by
      rw [mul_pow, show √2 ^ 3 = √2 ^ 2 * √2 by ring, hq2s]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hc (by linarith : (0:ℝ) ≤ 128 * √2 - 1)]
  have hsub1 : Set.Icc t₁ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left (h53.trans h31)
  obtain ⟨hd1p, hd1⟩ := bn_near Ω hlo hneg.le a t₁ t₀ h10 (fun s hs => hpos s (hsub1 hs))
    (fun s hs => hdiff s (hsub1 hs)) hH₀ (fun s hs => hH s (hsub1 hs)) hz1
  have hd5 := bn_far Ω hlo hneg.le a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH hz3 hz5
  have hd5p : 0 < lumDistFlat a t₀ t₅ := lt_of_lt_of_le (by positivity) hd5
  have h := ratio_step _ _ _ _ c hd1p hd5p hp1 hp5 hm1 hm5
  -- the log-polynomial at the three sources
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * Real.log 2 / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * Real.log 2 / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * Real.log 2 / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  obtain ⟨P1, hP1def⟩ : ∃ P : ℝ, P = 1 * Real.log 2 / 2 + a₂ / Real.log 10 * (1 * Real.log 2 / 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (1 * Real.log 2 / 2) ^ 3 := ⟨_, rfl⟩
  obtain ⟨P3, hP3def⟩ : ∃ P : ℝ, P = 3 * Real.log 2 / 2 + a₂ / Real.log 10 * (3 * Real.log 2 / 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2 / 2) ^ 3 := ⟨_, rfl⟩
  obtain ⟨P5, hP5def⟩ : ∃ P : ℝ, P = 5 * Real.log 2 / 2 + a₂ / Real.log 10 * (5 * Real.log 2 / 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (5 * Real.log 2 / 2) ^ 3 := ⟨_, rfl⟩
  have hL1 : logPolyDL3 a₂ a₃ H (√2 - 1) = P1 / H := by
    rw [hP1def]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 : logPolyDL3 a₂ a₃ H (2 * √2 - 1) = P3 / H := by
    rw [hP3def]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 : logPolyDL3 a₂ a₃ H (4 * √2 - 1) = P5 / H := by
    rw [hP5def]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  rw [hz3, hL3] at hp3
  have hP3 : 0 < P3 := (div_pos_iff_of_pos_right hHp).1 hp3
  rw [hz5, hL5] at hp5
  have hP5 : 0 < P5 := (div_pos_iff_of_pos_right hHp).1 hp5
  rw [hz1, hz5, hL1, hL5] at h
  rw [hz1, hL1] at hp1
  have hP1 : 0 < P1 := (div_pos_iff_of_pos_right hHp).1 hp1
  -- the distance bounds turn the two residuals into 18 κ P₁ ≤ 0.42 P₅
  have k1 : (4 * √2 * (9 / 2) / hubble a t₀) * (P1 / H) ≤ lumDistFlat a t₀ t₅ * (P1 / H) :=
    mul_le_mul_of_nonneg_right hd5 (by positivity)
  have k2 : lumDistFlat a t₀ t₁ * (P5 / H) ≤ (√2 * (21 / 50) / hubble a t₀) * (P5 / H) :=
    mul_le_mul_of_nonneg_right hd1 (by positivity)
  have k3 : 95499 / 100000 * ((4 * √2 * (9 / 2) / hubble a t₀) * (P1 / H))
      ≤ (√2 * (21 / 50) / hubble a t₀) * (P5 / H) := by
    have := mul_le_mul_of_nonneg_left k1 (by norm_num : (0:ℝ) ≤ 95499 / 100000)
    linarith
  have hX : 0 < √2 / (hubble a t₀ * H) := by positivity
  have hH0p := hH₀
  have e1 : 95499 / 100000 * ((4 * √2 * (9 / 2) / hubble a t₀) * (P1 / H))
      = √2 / (hubble a t₀ * H) * (95499 / 100000 * 18 * P1) := by field_simp; ring
  have e2 : (√2 * (21 / 50) / hubble a t₀) * (P5 / H) = √2 / (hubble a t₀ * H) * (21 / 50 * P5) := by
    field_simp
  rw [e1, e2] at k3
  have key : 95499 / 100000 * 18 * P1 ≤ 21 / 50 * P5 := le_of_mul_le_mul_left k3 hX
  -- displacement from the ΛCDM-implied point, rescaled
  obtain ⟨e₂, he₂⟩ : ∃ e : ℝ, e = (a₂ / Real.log 10 - (3 / 2 - 3 / 4 * Ω)) * Real.log 2 ^ 2 := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e : ℝ,
      e = (a₃ / Real.log 10 ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * Real.log 2 ^ 3 := ⟨_, rfl⟩
  have hQ1 : P1 = Qf Ω (1 * Real.log 2 / 2) + 1 / 4 * e₂ + 1 / 8 * e₃ := by
    rw [hP1def, he₂, he₃]; unfold Qf; ring
  have hQ3 : P3 = Qf Ω (3 * Real.log 2 / 2) + 9 / 4 * e₂ + 27 / 8 * e₃ := by
    rw [hP3def, he₂, he₃]; unfold Qf; ring
  have hQ5 : P5 = Qf Ω (5 * Real.log 2 / 2) + 25 / 4 * e₂ + 125 / 8 * e₃ := by
    rw [hP5def, he₂, he₃]; unfold Qf; ring
  have q1 := Qb1 Ω h1
  have q3 := Qb3 Ω h1
  have q5 := Qb5 Ω h1
  have hΩ2 : Ω ^ 2 ≤ 1 / 32400 := by
    nlinarith only [mul_pos (neg_pos.2 hneg) (by linarith : (0:ℝ) < Ω + 1 / 180), hlo, hneg]
  have hΩ2' : 0 ≤ Ω ^ 2 := sq_nonneg Ω
  have hfin : (1044 / 10000 : ℝ) ≤ 20 / 3 * e₃ - e₂ := by
    linarith only [key, hP3, hQ1, hQ3, hQ5, q1.1, q3.2, q5.2, hlo, hneg, hΩ2, hΩ2']
  exact conclude Ω a₂ a₃ e₂ e₃ he₂ he₃ hfin

/-- `B1FitRL19.box_neg` without its lower density bound, the upper bound on `a₂` and the lower bound on `a₃`: the
direction functional is negative wherever `a₂ ≥ 343/100` and `a₃ ≤ 169/100`, for every `Ω ≤ 1` (it decreases in `a₂`
and increases in `a₃`; the quadratic in `Ω` is concave with its maximum near forty-nine sixtieths). -/
lemma bn_box_neg (Ω a₂ a₃ l L : ℝ) (hΩ1 : Ω ≤ 1)
    (ha₂ : 343 / 100 ≤ a₂) (ha₃ : a₃ ≤ 169 / 100)
    (hl1 : 2302 / 1000 ≤ l) (hl2 : l ≤ 23027 / 10000)
    (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    20 / 3 * L * (a₃ - l ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6))
      - (a₂ - l * (3 / 2 - 3 / 4 * Ω)) < 0 := by
  set A3 := 9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6 with hA3
  set A2 := 3 / 2 - 3 / 4 * Ω with hA2
  have hA3p : 5 / 18 ≤ A3 := by nlinarith [sq_nonneg (Ω - 8 / 9)]
  have hA2p : 0 ≤ A2 := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hL0 : 0 ≤ L := by linarith
  have e1 : L * a₃ ≤ 30105 / 100000 * (169 / 100) := by
    rcases le_total 0 a₃ with h | h
    · exact mul_le_mul hL2 ha₃ h (by norm_num)
    · nlinarith [mul_nonneg hL0 (neg_nonneg.2 h)]
  have hll : (2302 / 1000 : ℝ) ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ (by norm_num) hl1 2
  have e2a : 30101 / 100000 * (2302 / 1000) ^ 2 ≤ L * l ^ 2 :=
    mul_le_mul hL1 hll (by positivity) hL0
  have e2 : 30101 / 100000 * (2302 / 1000) ^ 2 * A3 ≤ L * l ^ 2 * A3 :=
    mul_le_mul_of_nonneg_right e2a (by linarith)
  have e3 : l * A2 ≤ 23027 / 10000 * A2 := mul_le_mul_of_nonneg_right hl2 hA2p
  have hq : 30105 / 100000 * (169 / 100) * (20 / 3) - 343 / 100 + 23027 / 10000 * A2
      - 20 / 3 * (30101 / 100000 * (2302 / 1000) ^ 2 * A3) < 0 := by
    rw [hA2, hA3]; nlinarith [sq_nonneg (Ω - 49 / 60)]
  have e : 20 / 3 * L * (a₃ - l ^ 2 * A3) - (a₂ - l * A2)
      = 20 / 3 * (L * a₃) - 20 / 3 * (L * l ^ 2 * A3) - a₂ + l * A2 := by ring
  rw [e]; nlinarith

/-- Without `0 ≤ Ω`: the direction holds for every `Ω ≤ 1` (`fit_direction_r1`) and the box lies on the other side
of the line for every such `Ω` (`bn_box_neg`). -/
theorem rl19_box_unmatched_r1 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 1 := by
  intro Ω hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c ha₂l ha₂u ha₃l ha₃u hHp
    hp₁ hp₃ hp₅
  rintro ⟨hm₁, hm₃, hm₅⟩
  have hf := fit_direction_r1 Ω hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff
    hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c hHp hp₁ hp₃ hp₅ hm₁ hm₃ hm₅
  obtain ⟨hL1, hL2⟩ := Checked.Cosmography.B1FitWitness.t_bounds
  have hl1 := Checked.Cosmography.B1Fit.log_ten_ge
  have hl2 := Checked.Cosmography.B1FitWitness.log_ten_le
  have hneg := bn_box_neg Ω a₂ a₃ (Real.log 10) (Real.logb 10 2) hΩ₁ ha₂l ha₃u
    (by norm_num at hl1 ⊢; linarith) (by norm_num at hl2 ⊢; linarith) hL1 hL2
  unfold lusA2 lusA3 at hf
  nlinarith

/-- Without `a₂ ≤ 349/100`: the direction functional decreases in `a₂`, so a larger `a₂` stays on the other side of
the line (`bn_box_neg`). -/
theorem rl19_box_unmatched_r14 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 14 := by
  intro Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c ha₂l ha₃l ha₃u hHp
    hp₁ hp₃ hp₅
  rintro ⟨hm₁, hm₃, hm₅⟩
  have hf := Checked.Cosmography.B1Fit.fit_direction Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff
    hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c hHp hp₁ hp₃ hp₅ hm₁ hm₃ hm₅
  obtain ⟨hL1, hL2⟩ := Checked.Cosmography.B1FitWitness.t_bounds
  have hl1 := Checked.Cosmography.B1Fit.log_ten_ge
  have hl2 := Checked.Cosmography.B1FitWitness.log_ten_le
  have hneg := bn_box_neg Ω a₂ a₃ (Real.log 10) (Real.logb 10 2) hΩ₁ ha₂l ha₃u
    (by norm_num at hl1 ⊢; linarith) (by norm_num at hl2 ⊢; linarith) hL1 hL2
  unfold lusA2 lusA3 at hf
  nlinarith

/-- Without `157/100 ≤ a₃`: the direction functional increases in `a₃`, so a smaller `a₃` stays on the other side
of the line (`bn_box_neg`). -/
theorem rl19_box_unmatched_r15 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 15 := by
  intro Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c ha₂l ha₂u ha₃u hHp
    hp₁ hp₃ hp₅
  rintro ⟨hm₁, hm₃, hm₅⟩
  have hf := Checked.Cosmography.B1Fit.fit_direction Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff
    hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c hHp hp₁ hp₃ hp₅ hm₁ hm₃ hm₅
  obtain ⟨hL1, hL2⟩ := Checked.Cosmography.B1FitWitness.t_bounds
  have hl1 := Checked.Cosmography.B1Fit.log_ten_ge
  have hl2 := Checked.Cosmography.B1FitWitness.log_ten_le
  have hneg := bn_box_neg Ω a₂ a₃ (Real.log 10) (Real.logb 10 2) hΩ₁ ha₂l ha₃u
    (by norm_num at hl1 ⊢; linarith) (by norm_num at hl2 ⊢; linarith) hL1 hL2
  unfold lusA2 lusA3 at hf
  nlinarith

/-- `|5 ln Y / l| ≤ 1/20` for `Y` within `[978/1000, 10225/10000]` and `l ≥ 2302/1000`. -/
lemma bn_log_small (Y l : ℝ) (hY : 978 / 1000 ≤ Y ∧ Y ≤ 10225 / 10000) (hl : 2302 / 1000 ≤ l) :
    |5 * Real.log Y / l| ≤ 1 / 20 := by
  have hYp : 0 < Y := by linarith
  have hu : Real.log Y ≤ 225 / 10000 := by linarith [Real.log_le_sub_one_of_pos hYp]
  have hlo : -(11 / 489) ≤ Real.log Y := by
    have h1 := Real.one_sub_inv_le_log_of_pos hYp
    have h2 : Y⁻¹ ≤ (978 / 1000)⁻¹ := inv_anti₀ (by norm_num) hY.1
    norm_num at h2; linarith
  have hl0 : 0 < l := by linarith
  rw [abs_le]; constructor
  · rw [le_div_iff₀ hl0]; nlinarith
  · rw [div_le_iff₀ hl0]; nlinarith

/-- The residual against an offset shifted by `5 log₁₀(102/100)`. -/
lemma bn_shift (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    5 * Real.logb 10 X - (5 * Real.logb 10 Y + 5 * Real.logb 10 (102 / 100))
      = 5 * Real.log (X / Y / (102 / 100)) / Real.log 10 := by
  unfold Real.logb
  rw [Real.log_div (div_pos hX hY).ne' (by norm_num), Real.log_div hX.ne' hY.ne']
  ring

set_option maxHeartbeats 1000000 in
/-- Without `a₃ ≤ 169/100`: at density one fifth (`B1FitWitness.exists_model`) the cubic `a₂ = 343/100` (the lower
corner of the box), `a₃ = 117/20`, `H = 1` matches all three distance moduli within a twentieth of a magnitude, the
offset being the residual at the middle source plus `5 log₁₀(102/100)` (enclosures `B1FitWitness.WL1` … `WU5`). -/
theorem rl19_box_unmatched_h16 : necessity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 16 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, hz₁, hz₃, hz₅⟩ := Checked.Cosmography.B1FitWitness.exists_model
  have hΩ0 : (0:ℝ) ≤ 1 / 5 := by norm_num
  have hΩ1 : (1:ℝ) / 5 ≤ 1 := by norm_num
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  have h₃₀ : t₃ ≤ t₀ := le_trans h31 h10
  have h₅₀ : t₅ ≤ t₀ := le_trans h53 h₃₀
  have hsub1 : Set.Icc t₁ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left (le_trans h53 h31)
  have hsub3 : Set.Icc t₃ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left h53
  have hbr1 := lumDistFlat_flatLCDM (1/5) hΩ0 hΩ1 a t₁ t₀ h10 (fun s hs => hpos s (hsub1 hs))
    (fun s hs => hdiff s (hsub1 hs)) hH₀ (fun s hs => hH s (hsub1 hs))
  have hbr3 := lumDistFlat_flatLCDM (1/5) hΩ0 hΩ1 a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub3 hs))
    (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH s (hsub3 hs))
  have hbr5 := lumDistFlat_flatLCDM (1/5) hΩ0 hΩ1 a t₅ t₀ h₅₀ hpos hdiff hH₀ hH
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha1 : 0 < a t₁ := hpos t₁ ⟨le_trans h53 h31, h10⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h53, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₁ t₀ _ ha1 ha₀ hz₁, es1, hz₁, es1] at hbr1
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hbr3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hbr5
  change lumDistFlat a t₀ t₁ = √2 / hubble a t₀ * ∫ v in √(1 / √2)..1, gL (1/5) v at hbr1
  change lumDistFlat a t₀ t₃ = 2 * √2 / hubble a t₀ * ∫ v in √(1 / (2 * √2))..1, gL (1/5) v
    at hbr3
  change lumDistFlat a t₀ t₅ = 4 * √2 / hubble a t₀ * ∫ v in √(1 / (4 * √2))..1, gL (1/5) v
    at hbr5
  set J1 := ∫ v in √(1 / √2)..1, gL (1/5) v with hJ1
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL (1/5) v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL (1/5) v with hJ5
  set H₀ := hubble a t₀ with hH₀def
  -- enclosures of the three integrals at Ω = 1/5
  have hs1 : 1 < √2 := by linarith
  obtain ⟨hw1p, hw1⟩ := w_lt_one _ hs1
  obtain ⟨hw3p, hw3⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw5⟩ := w_lt_one (4 * √2) (by linarith)
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq2
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have eJ1 : (1926847473 / 5000000000 : ℝ) ≤ J1 ∧ J1 ≤ 385504523 / 1000000000 := by
    constructor
    · have := Checked.Cosmography.B1FitWitness.WL1 (1/5) hΩ0 hΩ1
      have := J_shift (1/5) hΩ0 hΩ1 _ _ hw1p wb1l (by norm_num)
      norm_num at *; linarith
    · have := Checked.Cosmography.B1FitWitness.WU1 (1/5) le_rfl le_rfl
      have := J_shift (1/5) hΩ0 hΩ1 _ _ (by norm_num) wb1u hw1.le
      norm_num at *; linarith
  have eJ3 : (1262414489 / 1000000000 : ℝ) ≤ J3 ∧ J3 ≤ 3160225433 / 2500000000 := by
    constructor
    · have := Checked.Cosmography.B1FitWitness.WL3 (1/5) hΩ0 hΩ1
      have := J_shift (1/5) hΩ0 hΩ1 _ _ hw3p wb3l (by norm_num)
      norm_num at *; linarith
    · have := Checked.Cosmography.B1FitWitness.WU3 (1/5) le_rfl le_rfl
      have := J_shift (1/5) hΩ0 hΩ1 _ _ (by norm_num) wb3u hw3.le
      norm_num at *; linarith
  have eJ5 : (10060897683 / 5000000000 : ℝ) ≤ J5 ∧ J5 ≤ 10078611121 / 5000000000 := by
    constructor
    · have := Checked.Cosmography.B1FitWitness.WL5 (1/5) hΩ0 hΩ1
      have := J_shift (1/5) hΩ0 hΩ1 _ _ hw5p wb5l (by norm_num)
      norm_num at *; linarith
    · have := Checked.Cosmography.B1FitWitness.WU5 (1/5) le_rfl le_rfl
      have := J_shift (1/5) hΩ0 hΩ1 _ _ (by norm_num) wb5u hw5.le
      norm_num at *; linarith
  -- the cubic a₂ = 343/100, a₃ = 117/20, H = 1
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  set t := ℓ / l with ht
  obtain ⟨htl, htu⟩ := Checked.Cosmography.B1FitWitness.t_bounds
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  set p1 := 1 / 2 + 343 / 100 * (1 / 4) * t + 117 / 20 * (1 / 8) * t ^ 2 with hp1
  set p3 := 3 / 2 + 343 / 100 * (9 / 4) * t + 117 / 20 * (27 / 8) * t ^ 2 with hp3
  set p5 := 5 / 2 + 343 / 100 * (25 / 4) * t + 117 / 20 * (125 / 8) * t ^ 2 with hp5
  have hL1 : logPolyDL3 (343/100) (117/20) 1 (redshift a t₀ t₁) = ℓ * p1 := by
    rw [hz₁, lp_eq _ _ 1 _ _ one_ne_zero hu1, hp1, ht]; field_simp; ring
  have hL3 : logPolyDL3 (343/100) (117/20) 1 (redshift a t₀ t₃) = ℓ * p3 := by
    rw [hz₃, lp_eq _ _ 1 _ _ one_ne_zero hu3, hp3, ht]; field_simp; ring
  have hL5 : logPolyDL3 (343/100) (117/20) 1 (redshift a t₀ t₅) = ℓ * p5 := by
    rw [hz₅, lp_eq _ _ 1 _ _ one_ne_zero hu5, hp5, ht]; field_simp; ring
  have ep1 := Checked.Cosmography.B1FitWitness.pq_bounds (1 / 2) (343 / 100 * (1 / 4)) (117 / 20 * (1 / 8)) t (by norm_num) (by norm_num)
    htl htu
  have ep3 := Checked.Cosmography.B1FitWitness.pq_bounds (3 / 2) (343 / 100 * (9 / 4)) (117 / 20 * (27 / 8)) t (by norm_num) (by norm_num)
    htl htu
  have ep5 := Checked.Cosmography.B1FitWitness.pq_bounds (5 / 2) (343 / 100 * (25 / 4)) (117 / 20 * (125 / 8)) t (by norm_num)
    (by norm_num) htl htu
  have hp1p : 0 < p1 := lt_of_lt_of_le (by norm_num) ep1.1
  have hp3p : 0 < p3 := lt_of_lt_of_le (by norm_num) ep3.1
  have hp5p : 0 < p5 := lt_of_lt_of_le (by norm_num) ep5.1
  have hJ1p : 0 < J1 := by linarith [eJ1.1]
  have hJ3p : 0 < J3 := by linarith [eJ3.1]
  have hJ5p : 0 < J5 := by linarith [eJ5.1]
  -- the three distance-to-polynomial ratios X_k
  set X1 := (√2 / H₀ * J1) / (ℓ * p1) with hX1
  set X3 := (2 * √2 / H₀ * J3) / (ℓ * p3) with hX3
  set X5 := (4 * √2 / H₀ * J5) / (ℓ * p5) with hX5
  have hX1p : 0 < X1 := by positivity
  have hX3p : 0 < X3 := by positivity
  have hX5p : 0 < X5 := by positivity
  have hY13 : X1 / X3 = (J1 * p3) / (2 * (J3 * p1)) := by
    rw [hX1, hX3]; field_simp; try ring
  have hY53 : X5 / X3 = (2 * (J5 * p3)) / (J3 * p5) := by
    rw [hX5, hX3]; field_simp; try ring
  have r13 := Checked.Cosmography.B1FitWitness.ratio_encl J1 J3 p3 p1 _ _ _ _ _ _ _ _ (2 * (978 / 1000 * (102 / 100))) (2 * (10225 / 10000 * (102 / 100))) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) eJ1 eJ3 ep3 ep1 (by norm_num) (by norm_num)
    (by norm_num)
  have r53 := Checked.Cosmography.B1FitWitness.ratio_encl J5 J3 p3 p5 _ _ _ _ _ _ _ _ (978 / 1000 * (102 / 100) / 2) (10225 / 10000 * (102 / 100) / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) eJ5 eJ3 ep3 ep5 (by norm_num) (by norm_num)
    (by norm_num)
  have hYa : 978 / 1000 ≤ X1 / X3 / (102 / 100) ∧ X1 / X3 / (102 / 100) ≤ 10225 / 10000 := by
    rw [hY13]; constructor
    · rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]; linarith [r13.1]
    · rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by positivity)]; linarith [r13.2]
  have hYb : 978 / 1000 ≤ X5 / X3 / (102 / 100) ∧ X5 / X3 / (102 / 100) ≤ 10225 / 10000 := by
    rw [hY53]; constructor
    · rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]; linarith [r53.1]
    · rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by positivity)]; linarith [r53.2]
  have hYc : 978 / 1000 ≤ X3 / X3 / (102 / 100) ∧ X3 / X3 / (102 / 100) ≤ 10225 / 10000 := by
    rw [div_self hX3p.ne']; norm_num
  have hl2302 : (2302 / 1000 : ℝ) ≤ l := by
    have := Checked.Cosmography.B1Fit.log_ten_ge; norm_num at this ⊢; linarith
  have hm1 := bn_log_small _ l hYa hl2302
  have hm3 := bn_log_small _ l hYc hl2302
  have hm5 := bn_log_small _ l hYb hl2302
  rw [← bn_shift X1 X3 hX1p hX3p] at hm1
  rw [← bn_shift X3 X3 hX3p hX3p] at hm3
  rw [← bn_shift X5 X3 hX5p hX3p] at hm5
  refine ⟨1 / 5, hΩ0, hΩ1, a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, hz₁, hz₃, hz₅,
    343 / 100, 117 / 20, 1, 5 * Real.logb 10 X3 + 5 * Real.logb 10 (102 / 100), by norm_num, by norm_num,
    by norm_num, one_pos, ?_, ?_, ?_, ?_⟩
  · rw [hL1]; positivity
  · rw [hL3]; positivity
  · rw [hL5]; positivity
  · refine ⟨?_, ?_, ?_⟩
    · rw [hbr1, hL1]; exact hm1
    · rw [hbr3, hL3]; exact hm3
    · rw [hbr5, hL5]; exact hm5

end Checked.Trust.NCBN
