import Checked.Trust.NecessityBO
import Checked.Trust.NecessityBN
import Checked.Cosmography.B1FitRL19

/-!
# Hypothesis necessity, the third-coefficient headline of the B1 fit and the RL19 box: the sources and the density (trust track T2b)

Run 2026-11-25T0028Z. Four more hypotheses of `B1A3Bound.third_coefficient_lower_bound` (with `NecessityBP`, every
hypothesis of it is classified) and one of `B1FitRL19.rl19_box_unmatched`.

* **Positivity of the polynomial at the middle source is REDUNDANT** (`third_coefficient_lower_bound_r15`): with
  `u` the logarithm of two over twice the logarithm of ten, twenty-five times the cubic at three `u` minus nine
  times the cubic at five `u` is thirty `u` minus four hundred and fifty `a₃ u³`. If the value at the middle source
  is not positive while the value at the farthest source is, this combination is negative, so `a₃ u²` exceeds one
  fifteenth, which is more than the bound allows (`u²` is below a forty-fourth). No distance enters.
* **The residual condition at the nearest source is NEEDED** (`third_coefficient_lower_bound_h17`): in the
  Einstein–de Sitter model of `NecessityAR` the cubic with second coefficient fifty and third coefficient equal
  to the bound matches the distance moduli of the two farther sources within a twentieth of a magnitude (each
  ratio of distance to polynomial distance within two percent of one, `resid_band`).
* **The redshift of the nearest source is NEEDED** (`third_coefficient_lower_bound_h10`): that source placed at
  the middle one, the same cubic serves.
* **The lower density bound is REDUNDANT** (`third_coefficient_lower_bound_r1`): the route of
  `NCBN.fit_direction_r1` (no density at or below minus one in one hundred and eighty reaches the farthest source;
  above it the distances to the nearest and the farthest source are bounded by the empty model's) gives the
  same inequality between the polynomial values at those sources, and with the middle value positive it puts the
  rescaled third coefficient far above the bound.
* **In `B1FitRL19.rl19_box_unmatched` the redshift of the nearest source is REDUNDANT** (`rl19_box_unmatched_r10`):
  for a density in the unit interval the distance integral to the farthest source is at least the ratio of the
  interval lengths times the one to the middle source (`bq_ratio35`, the integrand decreases), while inside the box
  the polynomial grows by at most a factor two and sixty-five hundredths between them (`bq_box_ratio`); the two
  residual conditions there let the two distance ratios differ by less than five percent. The nearest source
  plays no part.

Numbers chosen by `runs/2026-11-25T0028Z/scripts/eds_a3.py` (exact rationals); Lean checks every one.
-/

namespace Checked.Trust.NCBQ

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Set
open Checked.Trust.NCAQ Checked.Trust.NCAR Checked.Trust.NCBL Checked.Trust.NCBI Checked.Trust.NCBN
open Checked.Cosmography.B1Fit (sqrt2_bounds w_lt_one Jpos gL_intInt)

/-- The algebra of the middle source: a non-positive cubic there and a positive one at the farthest source
force the third coefficient above the bound. -/
theorem nbq_mid (a₂ a₃ : ℝ)
    (h3 : Bc a₂ a₃ (3 / 2 * (Real.log 2 / Real.log 10)) ≤ 0)
    (h5 : 0 < Bc a₂ a₃ (5 / 2 * (Real.log 2 / Real.log 10))) : 13 / 5 < a₃ := by
  obtain ⟨m1, m2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10 with hlam
  unfold Bc at h3 h5
  have hlam0 : 0 < lam := by linarith
  -- 25 B(3u) − 9 B(5u) = 30 u − 450 a₃ u³ with u = lam / 2
  have hcomb : 0 < lam / 2 * (15 * a₃ * (lam / 2) ^ 2 - 1) := by nlinarith
  have hk : 1 < 15 * a₃ * (lam / 2) ^ 2 := by
    have := (pos_iff_pos_of_mul_pos hcomb).mp (by linarith)
    linarith
  by_contra ha
  push Not at ha
  have hsq : (lam / 2) ^ 2 ≤ (0.30105 / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hsq0 : 0 ≤ (lam / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- Without `0 < P(2√2 − 1)`: a non-positive value there already forces the bound (`nbq_mid`). -/
theorem third_coefficient_lower_bound_r15 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 15 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp5
    hm1 hm3 hm5
  rcases lt_or_ge 0 (logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) with hp3 | hp3
  · exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
      hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  rw [hz3, poly3_eq _ _ _ (3 / 2) _ log_2s2] at hp3
  rw [hz5, poly3_eq _ _ _ (5 / 2) _ log_4s2] at hp5
  have hL : 0 < Real.log 10 / H := div_pos (Real.log_pos (by norm_num)) hHp
  apply nbq_mid a₂ a₃
  · by_contra hb
    push Not at hb
    have := mul_pos hL hb
    linarith
  · by_contra hb
    push Not at hb
    have := mul_nonpos_of_nonneg_of_nonpos hL.le hb
    linarith

theorem B_q_1 : (1.291956 : ℝ) ≤ Bc (50 : ℝ) (13 / 5 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (50 : ℝ) (13 / 5 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (1.292282 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_q_3 : (10.88413 : ℝ) ≤ Bc (50 : ℝ) (13 / 5 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (50 : ℝ) (13 / 5 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (10.886996 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_q_5 : (30.175209 : ℝ) ≤ Bc (50 : ℝ) (13 / 5 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (50 : ℝ) (13 / 5 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (30.183278 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

/-- Without the residual condition at `1 + z = √2`: in the Einstein–de Sitter model the cubic with second
coefficient fifty and third coefficient equal to the bound matches at `2√2` and `4√2`. -/
theorem third_coefficient_lower_bound_h17 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 17 := by
  obtain ⟨o53, o31, o10, p5, -⟩ := ea_ord
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  obtain ⟨l1, l2⟩ := log10_bd
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (50 : ℝ), (13 / 5 : ℝ), 7.175, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_q_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_q_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_q_5.1 (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_q_3.1 B_q_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_q_5.1 B_q_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num

/-- Without the redshift of the nearest source: that source placed at the middle one (`1 + z = 2√2`); the cubic of
`third_coefficient_lower_bound_h17` matches both distinct sources. -/
theorem third_coefficient_lower_bound_h10 :
    necessity% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 10 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, tE (2 * √2), tE (2 * √2), 1, o53, le_rfl, le_trans o31 o10, hp, hd,
    hH₀, hH, ea_S3.1, ea_S5.1, (50 : ℝ), (13 / 5 : ℝ), 7.175, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_q_3.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_q_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_q_5.1 (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_q_3.1 B_q_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_q_3.1 B_q_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_q_5.1 B_q_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num

/-- Without `0 ≤ Ω`: a density at or below `−1/180` cannot reach the farthest source (`bi_unreach`); above it the
residuals at the nearest and the farthest source and the positive middle value give the bound (`bn_near`, `bn_far`). -/
theorem third_coefficient_lower_bound_r1 :
    dropped% Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound 1 := by
  intro Ω h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  rcases le_or_gt 0 Ω with h0 | hneg
  · exact Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  obtain ⟨hq2l, hq2u⟩ := Checked.Cosmography.B1Fit.sqrt2_bounds
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
  have h := Checked.Cosmography.B1Fit.ratio_step _ _ _ _ c hd1p hd5p hp1 hp5 hm1 hm5
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
    rw [hP1def]; exact Checked.Cosmography.B1Fit.lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 : logPolyDL3 a₂ a₃ H (2 * √2 - 1) = P3 / H := by
    rw [hP3def]; exact Checked.Cosmography.B1Fit.lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 : logPolyDL3 a₂ a₃ H (4 * √2 - 1) = P5 / H := by
    rw [hP5def]; exact Checked.Cosmography.B1Fit.lp_eq a₂ a₃ H _ _ hHp.ne' hu5
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
  -- the third coefficient from the two residuals and the middle value (no density enters)
  have hℓ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = a₂ / Real.log 10 * Real.log 2 ^ 2 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = a₃ / Real.log 10 ^ 2 * Real.log 2 ^ 3 := ⟨_, rfl⟩
  have eq1 : P1 = Real.log 2 / 2 + X / 4 + Y / 8 := by rw [hP1def, hX, hY]; ring
  have eq3 : P3 = 3 * Real.log 2 / 2 + 9 * X / 4 + 27 * Y / 8 := by rw [hP3def, hX, hY]; ring
  have eq5 : P5 = 5 * Real.log 2 / 2 + 25 * X / 4 + 125 * Y / 8 := by rw [hP5def, hX, hY]; ring
  have hYl : 9 / 10 * Real.log 2 < Y := by
    linarith only [key, hP3, eq1, eq3, eq5, hℓ]
  obtain ⟨m1, m2⟩ := lam_bd
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hYe : Y = a₃ * (Real.log 2 / Real.log 10) ^ 2 * Real.log 2 := by
    rw [hY]; field_simp
  by_contra ha
  push Not at ha
  have hsq : (Real.log 2 / Real.log 10) ^ 2 ≤ 0.30105 ^ 2 := pow_le_pow_left₀ (by linarith) m2 2
  have hsq0 : 0 ≤ (Real.log 2 / Real.log 10) ^ 2 := sq_nonneg _
  have h1' : a₃ * (Real.log 2 / Real.log 10) ^ 2 ≤ 13 / 5 * 0.30105 ^ 2 := by
    rcases le_total 0 a₃ with h | h
    · exact mul_le_mul ha hsq hsq0 (by norm_num)
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg h hsq0) (by norm_num)
  have h2' : Y ≤ 13 / 5 * 0.30105 ^ 2 * Real.log 2 := by
    rw [hYe]; exact mul_le_mul_of_nonneg_right h1' hℓ.le
  linarith only [hYl, h2', hℓ]

/-- The distance integral to the farthest source is at least `(1 − w₅)/(1 − w₃)` times the one to the middle
source (the integrand decreases). -/
theorem bq_ratio35 (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (1 - √(1 / (4 * √2))) * ∫ v in √(1 / (2 * √2))..1, gL Ω v ≤
      (1 - √(1 / (2 * √2))) * ∫ v in √(1 / (4 * √2))..1, gL Ω v := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  set w3 := √(1 / (2 * √2)) with hw3
  set w5 := √(1 / (4 * √2)) with hw5
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have h53 : w5 ≤ w3 := by
    rw [hw3, hw5]; apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hsplit : ∫ v in w5..1, gL Ω v = (∫ v in w5..w3, gL Ω v) + ∫ v in w3..1, gL Ω v :=
    (intervalIntegral.integral_add_adjacent_intervals (gL_intInt Ω h0 h1 _ _ hw5p h53)
      (gL_intInt Ω h0 h1 _ _ hw3p hw31.le)).symm
  have hanti := gL_anti Ω h0 h1 w5 1 hw5p
  -- above w₁ the integrand is at most its value at w₁, below at least
  have hA : ∫ v in w3..1, gL Ω v ≤ ∫ v in w3..1, gL Ω w3 := by
    apply intervalIntegral.integral_mono_on hw31.le (gL_intInt Ω h0 h1 _ _ hw3p hw31.le)
      intervalIntegrable_const
    intro v hv
    exact hanti ⟨h53, le_rfl.trans hw31.le⟩ ⟨h53.trans hv.1, hv.2⟩ hv.1
  have hB : ∫ v in w5..w3, gL Ω w3 ≤ ∫ v in w5..w3, gL Ω v := by
    apply intervalIntegral.integral_mono_on h53 intervalIntegrable_const
      (gL_intInt Ω h0 h1 _ _ hw5p h53)
    intro v hv
    exact hanti ⟨hv.1, hv.2.trans hw31.le⟩ ⟨h53, hw31.le⟩ hv.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
  rw [hsplit]
  have hg : 0 ≤ gL Ω w3 := gL_nonneg Ω w3
  nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ w3 - w5),
    mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ 1 - w3)]


/-- Inside the RL19 box the polynomial distance grows by at most a factor two and sixty-five hundredths from the
middle to the farthest source. -/
theorem bq_box_ratio (a₂ a₃ : ℝ) (ha₂u : a₂ ≤ 349 / 100) (ha₃u : a₃ ≤ 169 / 100) :
    Bc a₂ a₃ (5 / 2 * (Real.log 2 / Real.log 10)) ≤ 265 / 100 * Bc a₂ a₃ (3 / 2 * (Real.log 2 / Real.log 10)) := by
  obtain ⟨m1, m2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have hl0 : 0 < lam := by linarith
  have e2 : a₂ * lam ≤ 349 / 100 * 0.30105 := mul_le_mul ha₂u m2 hl0.le (by norm_num)
  have hsq : lam ^ 2 ≤ 0.30105 ^ 2 := pow_le_pow_left₀ hl0.le m2 2
  have e3 : a₃ * lam ^ 2 ≤ 169 / 100 * 0.30105 ^ 2 := mul_le_mul ha₃u hsq (sq_nonneg _) (by norm_num)
  have key : -(1475 / 1000) + 2875 / 10000 * (a₂ * lam) + 668125 / 100000 * (a₃ * lam ^ 2) ≤ 0 := by
    linarith
  have := mul_nonpos_of_nonneg_of_nonpos hl0.le key
  unfold Bc
  nlinarith [this]

/-- Without the redshift of the nearest source: the residual conditions at the middle and the farthest source
alone exclude the box, for every density in the unit interval (`bq_ratio35`, `bq_box_ratio`). -/
theorem rl19_box_unmatched_r10 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 10 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz3 hz5 a₂ a₃ H c ha₂l ha₂u ha₃l ha₃u hHp
    hp1 hp3 hp5
  rintro ⟨-, hm3, hm5⟩
  obtain ⟨hq2l, hq2u⟩ := Checked.Cosmography.B1Fit.sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb3 := bl_bridge Ω h0 h1 a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  have hb5 := bl_bridge Ω h0 h1 a t₅ t₅ t₀ le_rfl (h53.trans (h31.trans h10)) hpos hdiff hH₀ hH
    (4 * √2) hz5
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by
    rw [hb3]; exact bl_pos Ω h0 h1 _ hw3p hw31 _ _ (by positivity) hH₀
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by
    rw [hb5]; exact bl_pos Ω h0 h1 _ hw5p hw51 _ _ (by positivity) hH₀
  have hr := Checked.Cosmography.B1Fit.ratio_step _ _ _ _ c hd3 hd5 hp3 hp5 hm3 hm5
  rw [hz3, poly3_eq _ _ _ (3 / 2) _ log_2s2] at hr hp3
  rw [hz5, poly3_eq _ _ _ (5 / 2) _ log_4s2] at hr hp5
  rw [hb3, hb5] at hr
  have hJ3 : 0 < ∫ v in √(1 / (2 * √2))..1, gL Ω v := Jpos Ω _ h0 h1 hw3p hw31
  have hJ5 : 0 < ∫ v in √(1 / (4 * √2))..1, gL Ω v := Jpos Ω _ h0 h1 hw5p hw51
  have hrat := bq_ratio35 Ω h0 h1
  have hbox := bq_box_ratio a₂ a₃ ha₂u ha₃u
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v
  set B3 := Bc a₂ a₃ (3 / 2 * (Real.log 2 / Real.log 10))
  set B5 := Bc a₂ a₃ (5 / 2 * (Real.log 2 / Real.log 10))
  have hK : 0 < Real.log 10 / H := div_pos (Real.log_pos (by norm_num)) hHp
  have hB3 : 0 < B3 := (pos_iff_pos_of_mul_pos hp3).mp hK
  have hX : 0 < √2 / hubble a t₀ * (Real.log 10 / H) := by positivity
  have e1 : 4 * √2 / hubble a t₀ * J5 * (Real.log 10 / H * B3)
      = √2 / hubble a t₀ * (Real.log 10 / H) * (4 * J5 * B3) := by ring
  have e2 : 2 * √2 / hubble a t₀ * J3 * (Real.log 10 / H * B5)
      = √2 / hubble a t₀ * (Real.log 10 / H) * (2 * J3 * B5) := by ring
  rw [e1, e2, ← mul_assoc, mul_comm (95499 / 100000 : ℝ), mul_assoc] at hr
  have k1 : 95499 / 100000 * (4 * J5 * B3) ≤ 2 * J3 * B5 := le_of_mul_le_mul_left hr hX
  have k2 : 2 * J3 * B5 ≤ 2 * J3 * (265 / 100 * B3) :=
    mul_le_mul_of_nonneg_left hbox (by positivity)
  have k3 : (95499 / 100000 * 4 * J5 - 2 * 265 / 100 * J3) * B3 ≤ 0 := by linarith
  have k4 : 95499 / 100000 * 4 * J5 - 2 * 265 / 100 * J3 ≤ 0 := by
    by_contra hk; push Not at hk; linarith [mul_pos hk hB3]
  obtain ⟨v3l, v3u⟩ := v3_bd
  obtain ⟨v5l, v5u⟩ := v5_bd
  have k5 : 5795 / 10000 * J3 ≤ (1 - √(1 / (4 * √2))) * J3 :=
    mul_le_mul_of_nonneg_right (by linarith) hJ3.le
  have k6 : (1 - √(1 / (2 * √2))) * J5 ≤ 4054 / 10000 * J5 :=
    mul_le_mul_of_nonneg_right (by linarith) hJ5.le
  linarith

end Checked.Trust.NCBQ
