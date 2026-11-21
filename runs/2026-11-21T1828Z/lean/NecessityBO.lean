import Checked.Trust.NecessityAS
import Checked.Trust.NecessityAP
import Checked.Trust.NecessityBN
import Work.Cosmography.B1A3Bound

/-! Scratch (run 2026-11-21T1828Z): hypothesis necessity of the third-coefficient bound from the witnesses and
lemmas of its parent statement. -/

namespace Checked.Trust.NCBO

open Set Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1
open Checked.Trust.NCAP Checked.Trust.NCL

theorem third_h3 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 3 := by
  obtain ⟨Ω, h0, h1, a, t5, t3, t1, t0, h31, h10, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, -, -, -,
    b4, hHp, p1, p3, p5, m⟩ := rl19_box_unmatched_h3
  obtain ⟨m1, m3, m5⟩ := m
  exact ⟨Ω, h0, h1, a, t5, t3, t1, t0, h31, h10, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, hHp, p1, p3,
    p5, m1, m3, m5, by norm_num at b4 ⊢; linarith⟩

theorem third_h4 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 4 := by
  obtain ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h10, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, -, -, -,
    b4, hHp, p1, p3, p5, m⟩ := rl19_box_unmatched_h4
  obtain ⟨m1, m3, m5⟩ := m
  exact ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h10, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, hHp, p1, p3,
    p5, m1, m3, m5, by norm_num at b4 ⊢; linarith⟩

theorem third_h5 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 5 := by
  obtain ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, -, -, -,
    b4, hHp, p1, p3, p5, m⟩ := rl19_box_unmatched_h5
  obtain ⟨m1, m3, m5⟩ := m
  exact ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, hHp, p1, p3,
    p5, m1, m3, m5, by norm_num at b4 ⊢; linarith⟩

theorem third_h11 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 11 := by
  obtain ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, h10, hp, hd, hH0, hH, z1, z5, a₂, a₃, H, c, -, -, -,
    b4, hHp, p1, p3, p5, m⟩ := Checked.Trust.NCAR.rl19_box_unmatched_h11
  obtain ⟨m1, m3, m5⟩ := m
  exact ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, h10, hp, hd, hH0, hH, z1, z5, a₂, a₃, H, c, hHp, p1, p3,
    p5, m1, m3, m5, by norm_num at b4 ⊢; linarith⟩

theorem third_h12 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 12 := by
  obtain ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, h10, hp, hd, hH0, hH, z1, z3, a₂, a₃, H, c, -, -, -,
    b4, hHp, p1, p3, p5, m⟩ := Checked.Trust.NCAS.rl19_box_unmatched_h12
  obtain ⟨m1, m3, m5⟩ := m
  exact ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, h10, hp, hd, hH0, hH, z1, z3, a₂, a₃, H, c, hHp, p1, p3,
    p5, m1, m3, m5, by norm_num at b4 ⊢; linarith⟩

theorem third_r6 : dropped% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 6 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans (h31.trans h10)) hdiff hH₀ hH with hp | hn
  · exact Work.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hp hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  · exact Work.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 (fun x => -a x) t₅ t₃ t₁ t₀ h53 h31 h10
      (pos_neg a t₅ t₀ hn) (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₅ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) (by rwa [redshift_neg]) a₂ a₃ H c hHp
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) (by rwa [redshift_neg])
      (by rwa [redshift_neg, lumDistFlat_neg]) (by rwa [redshift_neg, lumDistFlat_neg])
      (by rwa [redshift_neg, lumDistFlat_neg])

theorem third_r7 : dropped% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 7 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  exact Work.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5

theorem third_r8 : dropped% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 8 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  exact Work.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 (le_trans h31 h10)) hpos hdiff hH (hz5 ▸ z5_pos))
    hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5

theorem third_nv : nonvacuity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound := by
  obtain ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, h10, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, -, -, -,
    hHp, p1, p3, p5, m⟩ := Checked.Trust.NCBN.rl19_box_unmatched_h16
  obtain ⟨m1, m3, m5⟩ := m
  exact ⟨Ω, h0, h1, a, t5, t3, t1, t0, h53, h31, h10, hp, hd, hH0, hH, z1, z3, z5, a₂, a₃, H, c, hHp, p1,
    p3, p5, m1, m3, m5, trivial⟩

/-! ## Positivity of the cubic at the nearest and at the middle source -/

theorem bo_x_bd : 0 < Real.log 2 / Real.log 10 ∧ Real.log 2 / Real.log 10 < 8 / 25 := by
  obtain ⟨l1, l2⟩ := Checked.Trust.NCAQ.log10_bd
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have hl : 0 < Real.log 10 := by linarith
  refine ⟨div_pos (by linarith) hl, (div_lt_iff₀ hl).2 (by linarith)⟩

theorem bo_q (a₂ a₃ k x : ℝ) : Checked.Trust.NCAR.Bc a₂ a₃ (k * x) =
    (k * x) * (1 + a₂ * (k * x) + a₃ * (k * x) ^ 2) := by
  unfold Checked.Trust.NCAR.Bc; ring

/-- The cubic not positive at the nearest source but positive at the middle one forces a large third
coefficient. -/
theorem bo_alg1 (a₂ a₃ x : ℝ) (hx : 0 < x) (hx' : x < 8 / 25)
    (h1 : Checked.Trust.NCAR.Bc a₂ a₃ (1 / 2 * x) ≤ 0) (h3 : 0 < Checked.Trust.NCAR.Bc a₂ a₃ (3 / 2 * x)) :
    13 / 5 < a₃ := by
  rw [bo_q] at h1 h3
  have hu : 0 < 1 / 2 * x := by positivity
  have hv : 0 < 3 / 2 * x := by positivity
  have A : 1 + a₂ * (1 / 2 * x) + a₃ * (1 / 2 * x) ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hu h]
  have B : 0 < 1 + a₂ * (3 / 2 * x) + a₃ * (3 / 2 * x) ^ 2 := by
    by_contra h; push Not at h; nlinarith [mul_nonneg hv.le (neg_nonneg.2 h)]
  by_contra hc; push Not at hc
  have hx2 : x ^ 2 < (8 / 25) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg x)]

/-- The cubic not positive at the middle source but positive at the farthest one forces a large third
coefficient. -/
theorem bo_alg3 (a₂ a₃ x : ℝ) (hx : 0 < x) (hx' : x < 8 / 25)
    (h3 : Checked.Trust.NCAR.Bc a₂ a₃ (3 / 2 * x) ≤ 0) (h5 : 0 < Checked.Trust.NCAR.Bc a₂ a₃ (5 / 2 * x)) :
    13 / 5 < a₃ := by
  rw [bo_q] at h3 h5
  have hu : 0 < 3 / 2 * x := by positivity
  have hv : 0 < 5 / 2 * x := by positivity
  have A : 1 + a₂ * (3 / 2 * x) + a₃ * (3 / 2 * x) ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hu h]
  have B : 0 < 1 + a₂ * (5 / 2 * x) + a₃ * (5 / 2 * x) ^ 2 := by
    by_contra h; push Not at h; nlinarith [mul_nonneg hv.le (neg_nonneg.2 h)]
  by_contra hc; push Not at hc
  have hx2 : x ^ 2 < (8 / 25) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg x)]

theorem bo_pos_iff (a₂ a₃ H k z : ℝ) (hH : 0 < H) (hz : Real.log (1 + z) = k * Real.log 2) :
    0 < logPolyDL3 a₂ a₃ H z ↔ 0 < Checked.Trust.NCAR.Bc a₂ a₃ (k * (Real.log 2 / Real.log 10)) := by
  rw [Checked.Trust.NCAR.poly3_eq a₂ a₃ H k z hz]
  have : 0 < Real.log 10 / H := div_pos (Real.log_pos (by norm_num)) hH
  exact ⟨fun h => (pos_iff_pos_of_mul_pos h).1 this, fun h => mul_pos this h⟩

theorem third_r14 : dropped% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 14 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp3 hp5
    hm1 hm3 hm5
  by_cases hp1 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)
  · exact Work.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  · rw [hz1, bo_pos_iff a₂ a₃ H (1 / 2) _ hHp Checked.Trust.NCAR.log_s2] at hp1
    rw [hz3, bo_pos_iff a₂ a₃ H (3 / 2) _ hHp Checked.Trust.NCAQ.log_2s2] at hp3
    obtain ⟨x0, x1⟩ := bo_x_bd
    exact bo_alg1 a₂ a₃ _ x0 x1 (not_lt.1 hp1) hp3

theorem third_r15 : dropped% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 15 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp5
    hm1 hm3 hm5
  by_cases hp3 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)
  · exact Work.Cosmography.B1A3Bound.third_coefficient_lower_bound Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  · rw [hz3, bo_pos_iff a₂ a₃ H (3 / 2) _ hHp Checked.Trust.NCAQ.log_2s2] at hp3
    rw [hz5, bo_pos_iff a₂ a₃ H (5 / 2) _ hHp Checked.Trust.NCAQ.log_4s2] at hp5
    obtain ⟨x0, x1⟩ := bo_x_bd
    exact bo_alg3 a₂ a₃ _ x0 x1 (not_lt.1 hp3) hp5

/-! ## The distance-modulus conditions and the redshift of the nearest source (Einstein–de Sitter witnesses) -/

section EdS
open Checked.Trust.NCAQ Checked.Trust.NCAR

theorem B_bo_1 : (6.952849 : ℝ) ≤ Bc (300 : ℝ) (2 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (300 : ℝ) (2 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (6.954679 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_bo_3 : (61.79535 : ℝ) ≤ Bc (300 : ℝ) (2 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (300 : ℝ) (2 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (61.81174 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_bo_5 : (171.492988 : ℝ) ≤ Bc (300 : ℝ) (2 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (300 : ℝ) (2 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (171.538583 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

/-- Without the distance-modulus condition at the nearest source: in the Einstein–de Sitter model the cubic
`a₂ = 300`, `a₃ = 2` matches the distance moduli at the middle and farthest sources. -/
theorem third_h17 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 17 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (300 : ℝ), (2 : ℝ), 407547 / 10000, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_bo_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_bo_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_bo_5.1 (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_bo_3.1 B_bo_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_bo_5.1 B_bo_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Without the redshift of the nearest source: that source placed at the middle one, in the Einstein–de Sitter
model, with the cubic of `third_h17`. -/
theorem third_h10 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 10 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  have m3 : |5 * Real.logb 10 (lumDistFlat ea 1 (tE (2 * √2)) / logPolyDL3 (300 : ℝ) (2 : ℝ)
      (407547 / 10000) (redshift ea 1 (tE (2 * √2)))) - 0| ≤ 1 / 20 := by
    rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_bo_3.1 B_bo_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q3 : 0 < logPolyDL3 (300 : ℝ) (2 : ℝ) (407547 / 10000) (redshift ea 1 (tE (2 * √2))) := by
    rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_bo_3.1 (by norm_num) (by norm_num)
  refine ⟨1, by norm_num, le_rfl, ea, _, tE (2 * √2), tE (2 * √2), 1, o53, le_rfl, le_trans o31 o10, hp, hd,
    hH₀, hH, ea_S3.1, ea_S5.1, (300 : ℝ), (2 : ℝ), 407547 / 10000, 0, by norm_num, q3, q3, ?_, m3, m3, ?_,
    by norm_num⟩
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_bo_5.1 (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_bo_5.1 B_bo_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Without the distance-modulus condition at the middle source: in the Einstein–de Sitter model the cubic `a₂ = 171/4`, `a₃ = −23` (as in `Checked.Trust.NCAR.fit_direction_h18`) matches at the nearest and farthest sources. -/
theorem third_h18 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 18 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (171 / 4 : ℝ), (-23 : ℝ), 3.5495, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
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

/-- Without the distance-modulus condition at the farthest source: in the Einstein–de Sitter model the cubic `a₂ = 8`, `a₃ = −21/4` (as in `Checked.Trust.NCAR.fit_direction_h19`) matches at the nearest and middle sources. -/
theorem third_h19 : necessity% Work.Cosmography.B1A3Bound.third_coefficient_lower_bound 19 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (8 : ℝ), (-21 / 4 : ℝ), 1.0706, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
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

end EdS

end Checked.Trust.NCBO
