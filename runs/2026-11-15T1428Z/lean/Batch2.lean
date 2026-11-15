import Checked.Trust.NecessityAP

open Set Filter Topology
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

namespace Checked.Trust.NCAP

theorem log_ten_gt : (5 / 3 : ℝ) < Real.log 10 := by
  have h2 := Real.log_two_gt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) < 10)
  linarith

/-- Near the ΛCDM coefficients (density at most two fifths, distance at most five quarters), the cubic log-polynomial is
positive at every positive redshift with one plus redshift at most ten. -/
theorem near_pos (Ω : ℝ) (h2 : Ω ≤ 2 / 5) (a₂ a₃ z : ℝ) (hz : 0 < z)
    (hz10 : 1 + z ≤ 10)
    (hd : (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 ≤ (5 / 4) ^ 2) :
    0 < Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3 := by
  have hL : 0 < Real.logb 10 (1 + z) := Real.logb_pos (by norm_num) (by linarith)
  have hL1 : Real.logb 10 (1 + z) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]; simpa using hz10
  have hl := log_ten_gt
  have hA2 : 2 ≤ lusA2 Ω := by unfold lusA2; nlinarith
  have hA3 : 0 ≤ lusA3 Ω := by
    unfold lusA3; exact mul_nonneg (sq_nonneg _) (by nlinarith)
  set L := Real.logb 10 (1 + z)
  have d2 : |a₂ - lusA2 Ω| ≤ 5 / 4 := by
    rw [← Real.sqrt_sq_eq_abs]; rw [show (5 / 4 : ℝ) = √((5 / 4) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a₃ - lusA3 Ω)])
  have d3 : |a₃ - lusA3 Ω| ≤ 5 / 4 := by
    rw [← Real.sqrt_sq_eq_abs]; rw [show (5 / 4 : ℝ) = √((5 / 4) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a₂ - lusA2 Ω)])
  have e2 := (abs_le.1 d2).1
  have e3 := (abs_le.1 d3).1
  have hL2 : 0 < L ^ 2 := by positivity
  have hL3 : L ^ 3 ≤ L ^ 2 := by
    rw [show L ^ 3 = L ^ 2 * L by ring]; exact mul_le_of_le_one_right hL2.le hL1
  have k2 : (3 / 4) * L ^ 2 ≤ a₂ * L ^ 2 := by nlinarith
  have k3 : -(5 / 4) * L ^ 3 ≤ a₃ * L ^ 3 := by nlinarith [pow_pos hL 3]
  nlinarith

theorem H_pos_of (a₂ a₃ H z : ℝ)
    (hP : 0 < Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)
    (h : 0 < logPolyDL3 a₂ a₃ H z) : 0 < H := by
  unfold logPolyDL3 at h
  have h1 : 0 < Real.log 10 / H := (pos_iff_pos_of_mul_pos h).2 hP
  exact (div_pos_iff_of_pos_left (Real.log_pos (by norm_num))).1 h1

theorem lp_pos_of (a₂ a₃ H z : ℝ) (hH : 0 < H)
    (hP : 0 < Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3) :
    0 < logPolyDL3 a₂ a₃ H z := by
  unfold logPolyDL3; exact mul_pos (div_pos (Real.log_pos (by norm_num)) hH) hP

theorem cubic_separation_r11 : dropped% Checked.Cosmography.B1Sep.cubic_separation 11 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH₀ hH hz3 hz7 a₂ a₃ H c hp3 hp7 hm3 hm7
  by_contra hd
  have hd' : (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 ≤ (5 / 4) ^ 2 := le_of_not_gt hd
  have hP := near_pos Ω h2 a₂ a₃ 3 (by norm_num) (by norm_num) hd'
  rw [hz3] at hp3
  have hHp := H_pos_of a₂ a₃ H 3 hP hp3
  rw [← hz3] at hp3
  exact hd (Checked.Cosmography.B1Sep.cubic_separation Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH₀ hH
    hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7)

theorem cubic_separation_r12 : dropped% Checked.Cosmography.B1Sep.cubic_separation 12 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH₀ hH hz3 hz7 a₂ a₃ H c hHp hp7 hm3 hm7
  by_contra hd
  have hd' : (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 ≤ (5 / 4) ^ 2 := le_of_not_gt hd
  have hp3 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃) := by
    rw [hz3]; exact lp_pos_of a₂ a₃ H 3 hHp (near_pos Ω h2 a₂ a₃ 3 (by norm_num) (by norm_num) hd')
  exact hd (Checked.Cosmography.B1Sep.cubic_separation Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH₀ hH
    hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7)

theorem cubic_separation_r13 : dropped% Checked.Cosmography.B1Sep.cubic_separation 13 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH₀ hH hz3 hz7 a₂ a₃ H c hHp hp3 hm3 hm7
  by_contra hd
  have hd' : (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 ≤ (5 / 4) ^ 2 := le_of_not_gt hd
  have hp7 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇) := by
    rw [hz7]; exact lp_pos_of a₂ a₃ H 7 hHp (near_pos Ω h2 a₂ a₃ 7 (by norm_num) (by norm_num) hd')
  exact hd (Checked.Cosmography.B1Sep.cubic_separation Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH₀ hH
    hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7)

/-- With nonnegative coefficients the cubic log-polynomial is positive at every positive redshift. -/
theorem box_pos (a₂ a₃ z : ℝ) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃) (hz : 0 < z) :
    0 < Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3 := by
  have hL : 0 < Real.logb 10 (1 + z) := Real.logb_pos (by norm_num) (by linarith)
  positivity

theorem rl19_box_unmatched_r17 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 17 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u
    hp1 hp3 hp5
  have q := sqrt2_gt
  have hp1' := hp1
  rw [hz1] at hp1'
  have hHp := H_pos_of a₂ a₃ H _ (box_pos a₂ a₃ _ (by linarith) (by linarith) (by linarith)) hp1'
  exact Checked.Cosmography.B1FitRL19.rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp hp1 hp3 hp5

theorem rl19_box_unmatched_r18 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 18 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u
    hHp hp3 hp5
  have q := sqrt2_gt
  exact Checked.Cosmography.B1FitRL19.rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp
    (by rw [hz1]; exact lp_pos_of a₂ a₃ H _ hHp (box_pos a₂ a₃ _ (by linarith) (by linarith) (by linarith)))
    hp3 hp5

theorem rl19_box_unmatched_r19 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 19 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u
    hHp hp1 hp5
  have q := sqrt2_gt
  exact Checked.Cosmography.B1FitRL19.rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp hp1
    (by rw [hz3]; exact lp_pos_of a₂ a₃ H _ hHp (box_pos a₂ a₃ _ (by linarith) (by linarith) (by linarith)))
    hp5

theorem rl19_box_unmatched_r20 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 20 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u
    hHp hp1 hp3
  have q := sqrt2_gt
  exact Checked.Cosmography.B1FitRL19.rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp hp1 hp3
    (by rw [hz5]; exact lp_pos_of a₂ a₃ H _ hHp (box_pos a₂ a₃ _ (by linarith) (by linarith) (by linarith)))

end Checked.Trust.NCAP
