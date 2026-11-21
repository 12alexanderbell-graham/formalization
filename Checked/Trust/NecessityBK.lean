import Checked.Cosmography.B1Separation
import Checked.Trust.NecessityAW
import Checked.Trust.NecessityBI
import Checked.Trust.NecessityBKCerts

/-!
# Hypothesis necessity, the five B1 headlines on the third-order polynomial: the lower density bound (trust track T2b)

Run 2026-11-21T0628Z. `B1.cubic_misses_z3`, `cubic_misses_z7`, `cubic_shape_miss`, `B1Sep.cubic_separation` and
`B1Sep.cubic_direction` assume flat ΛCDM with matter density between one fifth and two fifths. Their first
hypothesis, the lower density bound, is REDUNDANT in the first four and NEEDED in the last.

* **NEEDED in `cubic_direction`** (`cubic_direction_h1`): in de Sitter space (density zero, `a = exp`) the
  distances to the two sources are twelve and fifty-six over the Hubble rate; a cubic whose values at the two
  sources are in the same ratio has equal residuals there (the common offset absorbs them), and the cubic chosen
  near the one that vanishes at both sources lies on the other side of the line through the ΛCDM-implied point.
  Near that cubic the side is set by the sign of five halves of the ΛCDM polynomial at the nearer source minus
  its value at the farther one, which is negative for every density below about sixteen hundredths: the bound is
  not a convenience of the proof.
* **REDUNDANT in the other four, densities from zero to one fifth**: enclosures of the two distance integrals on
  five density pieces (`Checked/Trust/NecessityBKCerts.lean`, the method of `B1Truncation`), then the steps of
  the headlines' own proofs with the density bounded above only (`bk_z3_of`, `bk_z7_of`, `bk_shape_of`,
  `bk_case`, `bk_match`; the ΛCDM polynomial is positive and increasing for every density up to two fifths).
* **REDUNDANT in the other four, negative densities**: a density so negative that the radicand of the law is
  negative at a source admits no model reaching it (`bi_unreach`); otherwise, for a density at most zero the
  integrand is at least the empty model's, so from the time where the scale factor is a fixed fraction of its
  present value the distance is at least the empty model's (`bk_far`, intermediate value and `bi_lower`), and at
  redshift three it is at most eleven tenths of the empty model's (`bk_up3`, `bi_upper`). The misses only grow as
  the density falls.
-/

namespace Checked.Trust.NCBK

open Set Real
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1Sep
open Checked.Trust.NCBI Checked.Trust.NCBKC

theorem bk_redshift (k : ℝ) (hk : 0 < k) : redshift Real.exp 0 (-Real.log k) = k - 1 := by
  unfold redshift
  rw [Real.exp_zero, Real.exp_neg, Real.exp_log hk]; field_simp

theorem bk_comoving (k : ℝ) (hk : 0 < k) : comoving Real.exp 0 (-Real.log k) = k - 1 := by
  unfold comoving
  have h : (fun s => 1 / Real.exp s) = fun s => Real.exp (-s) := by
    funext s; rw [Real.exp_neg, one_div]
  rw [h, intervalIntegral.integral_comp_neg (fun s => Real.exp s), integral_exp]
  simp [Real.exp_log hk]

theorem bk_lumdist (k : ℝ) (hk : 0 < k) :
    lumDistFlat Real.exp 0 (-Real.log k) = k * (k - 1) := by
  unfold lumDistFlat
  rw [bk_redshift k hk, bk_comoving k hk, Real.exp_zero]; ring

/-- The cubic of the witness, in the variable `u = ln(1+z)`: coefficients `b₂ = −5/(6ℓ) − 31ℓ/1000`,
`b₃ = 1/(6ℓ²) + 29/1000` with `ℓ = ln 2`. -/
noncomputable def bkB2 : ℝ := -5 / (6 * Real.log 2) - 31 * Real.log 2 / 1000
noncomputable def bkB3 : ℝ := 1 / (6 * Real.log 2 ^ 2) + 29 / 1000

theorem bk_P (k : ℝ) :
    k * Real.log 2 + bkB2 * (k * Real.log 2) ^ 2 + bkB3 * (k * Real.log 2) ^ 3
      = k * Real.log 2 * ((k - 2) * (k - 3) / 6 + k * (29 * k - 31) / 1000 * Real.log 2 ^ 2) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold bkB2 bkB3
  field_simp
  ring

theorem bk_poly (m z : ℝ) (hz : Real.log (1 + z) = m * Real.log 2) :
    logPolyDL3 (Real.log 10 * bkB2) (Real.log 10 ^ 2 * bkB3) 1 z
      = m * Real.log 2 * ((m - 2) * (m - 3) / 6 + m * (29 * m - 31) / 1000 * Real.log 2 ^ 2) := by
  have hl : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [poly_gen _ _ _ _ one_ne_zero, hz, mul_div_cancel_left₀ _ hl,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hl), div_one, bk_P m]

theorem bk_l2 : (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧ Real.log 2 < 6931471808 / 10000000000 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

/-- Without `1/5 ≤ Ω`: de Sitter space and a cubic in the exact ratio of its two distances. -/
theorem cubic_direction_h1 : necessity% Checked.Cosmography.B1Sep.cubic_direction 1 := by
  have h4 : (0:ℝ) < 4 := by norm_num
  have h8 : (0:ℝ) < 8 := by norm_num
  have hz3 : redshift Real.exp 0 (-Real.log 4) = 3 := by rw [bk_redshift 4 h4]; norm_num
  have hz7 : redshift Real.exp 0 (-Real.log 8) = 7 := by rw [bk_redshift 8 h8]; norm_num
  have hP3 := bk_poly 2 3 log4
  have hP7 := bk_poly 3 7 log8
  have hD3 := bk_lumdist 4 h4
  have hD7 := bk_lumdist 8 h8
  obtain ⟨l1, l2⟩ := bk_l2
  have hl0 : 0 < Real.log 2 := by linarith
  have hH0 : hubble Real.exp 0 = 1 := by rw [Checked.Trust.NecessityAW.hubble_exp]
  have e73 : -Real.log 8 ≤ -Real.log 4 := by
    have := Real.log_le_log h4 (by norm_num : (4:ℝ) ≤ 8); linarith
  have e30 : -Real.log 4 ≤ 0 := by have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  have hX : lumDistFlat Real.exp 0 (-Real.log 8)
        / logPolyDL3 (Real.log 10 * bkB2) (Real.log 10 ^ 2 * bkB3) 1 (redshift Real.exp 0 (-Real.log 8))
      = lumDistFlat Real.exp 0 (-Real.log 4)
        / logPolyDL3 (Real.log 10 * bkB2) (Real.log 10 ^ 2 * bkB3) 1 (redshift Real.exp 0 (-Real.log 4)) := by
    rw [hz3, hz7, hP3, hP7, hD3, hD7]
    field_simp
    ring
  refine ⟨0, by norm_num, Real.exp, -Real.log 8, -Real.log 4, 0, e73, e30,
    fun s _ => Real.exp_pos s, fun s _ => Real.differentiableAt_exp, by rw [hH0]; norm_num, ?_, hz3, hz7,
    Real.log 10 * bkB2, Real.log 10 ^ 2 * bkB3, 1,
    5 * Real.logb 10 (lumDistFlat Real.exp 0 (-Real.log 4)
        / logPolyDL3 (Real.log 10 * bkB2) (Real.log 10 ^ 2 * bkB3) 1 (redshift Real.exp 0 (-Real.log 4))),
    one_pos, ?_, ?_, by simp, by rw [hX]; simp, ?_⟩
  · intro s _; rw [Checked.Trust.NecessityAW.hubble_exp]; simp
  · rw [hz3, hP3]; positivity
  · rw [hz7, hP7]; positivity
  · rw [not_lt]
    unfold lusA2 lusA3 bkB2 bkB3
    have hlb : Real.logb 10 2 = Real.log 2 / Real.log 10 := rfl
    rw [hlb]
    have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    rw [← sub_nonneg]
    have e : Real.log 10 * (-5 / (6 * Real.log 2) - 31 * Real.log 2 / 1000) - Real.log 10 * (3 / 2 - 3 / 4 * 0)
        - 7 * (Real.log 2 / Real.log 10) * (Real.log 10 ^ 2 * (1 / (6 * Real.log 2 ^ 2) + 29 / 1000)
          - Real.log 10 ^ 2 * (9 / 8 * 0 ^ 2 - 2 * 0 + 7 / 6))
        = Real.log 10 / Real.log 2 * (49 / 6 * Real.log 2 ^ 2 - 234 / 1000 * Real.log 2 ^ 2
          - 3 / 2 * Real.log 2 - 2) := by
      field_simp; ring
    rw [e]
    apply mul_nonneg (by positivity)
    nlinarith

/-! ## Below the density one fifth: the two misses and their difference -/

theorem bk_Qc_pos (Ω u : ℝ) (h2 : Ω ≤ 2 / 5) (hu : 0 < u) : 0 < Qc Ω u := by
  unfold Qc
  have hb2 : 0 ≤ 3 / 2 - 3 / 4 * Ω := by linarith
  have hb3 : 0 ≤ 9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6 := by nlinarith [sq_nonneg (Ω - 8 / 9)]
  positivity

theorem bk_Qc_mono (Ω u v : ℝ) (h2 : Ω ≤ 2 / 5) (hu : 0 ≤ u) (huv : u ≤ v) : Qc Ω u ≤ Qc Ω v := by
  unfold Qc
  have hb2 : 0 ≤ 3 / 2 - 3 / 4 * Ω := by linarith
  have hb3 : 0 ≤ 9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6 := by nlinarith [sq_nonneg (Ω - 8 / 9)]
  have e2 : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
  have e3 : u ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hu huv 3
  nlinarith [mul_le_mul_of_nonneg_left e2 hb2, mul_le_mul_of_nonneg_left e3 hb3]

/-- For a density at most zero, the distance to a source at least as far as the scale factor `w² a₀` is at
least that of the empty model to the time where `a = w² a₀`, scaled by `1 + z` (intermediate value, the bridge
`bi_bridge` from that time, and the comparison `bi_lower` with the empty model). -/
theorem bk_far (Ω : ℝ) (hΩ : Ω ≤ 0) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1) (hwt : a t ≤ w ^ 2 * a t₀)
    (hR : 0 < Ω + (1 - Ω) * w ^ 6) :
    (1 + redshift a t₀ t) * (1 / w ^ 2 - 1) ≤ lumDistFlat a t₀ t * hubble a t₀ := by
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨htt, le_rfl⟩
  have hat : 0 < a t := hpos t ⟨le_rfl, htt⟩
  have hcont : ContinuousOn a (Set.Icc t t₀) := fun x hx =>
    (hdiff x hx).continuousAt.continuousWithinAt
  have hw2 : w ^ 2 ≤ 1 := pow_le_one₀ hw0.le hw1
  have hin : w ^ 2 * a t₀ ∈ Set.Icc (a t) (a t₀) := ⟨hwt, by nlinarith⟩
  obtain ⟨s, hs, has⟩ := intermediate_value_Icc htt hcont hin
  have hsub : Set.Icc s t₀ ⊆ Set.Icc t t₀ := Set.Icc_subset_Icc_left hs.1
  have hsw : √(a s / a t₀) = w := by
    rw [has, mul_div_cancel_right₀ _ ha₀.ne']; exact Real.sqrt_sq hw0.le
  have hbs := bi_bridge Ω (by linarith) a s t₀ hs.2 (fun u hu => hpos u (hsub hu))
    (fun u hu => hdiff u (hsub hu)) hH₀ (fun u hu => hH u (hsub hu)) (by rw [hsw]; exact hR)
  rw [hsw] at hbs
  have hzs : 1 + redshift a t₀ s = 1 / w ^ 2 := by
    unfold redshift; rw [has]; field_simp; ring
  rw [hzs] at hbs
  have hlow := bi_lower Ω w 1 hΩ hw0 hw1 hR
  have hr1 : (1:ℝ) ^ 3 / √(Ω + (1 - Ω) * 1 ^ 6) = 1 := by simp
  rw [hr1, one_mul, show (1:ℝ) / 1 ^ 2 = 1 by norm_num] at hlow
  have hcom : comoving a t₀ s ≤ comoving a t₀ t := by
    unfold comoving
    have hc : ContinuousOn (fun u => 1 / a u) (Set.Icc t t₀) := fun x hx =>
      (continuousAt_const.div (hdiff x hx).continuousAt (hpos x hx).ne').continuousWithinAt
    have hi1 : IntervalIntegrable (fun u => 1 / a u) MeasureTheory.volume t s :=
      (hc.mono (Set.Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
    have hi2 : IntervalIntegrable (fun u => 1 / a u) MeasureTheory.volume s t₀ :=
      (hc.mono hsub).intervalIntegrable_of_Icc hs.2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have : 0 ≤ ∫ u in t..s, 1 / a u :=
      intervalIntegral.integral_nonneg hs.1 (fun u hu =>
        (div_pos one_pos (hpos u ⟨hu.1, le_trans hu.2 hs.2⟩)).le)
    linarith
  have hls : lumDistFlat a t₀ s = a t₀ * (1 / w ^ 2) * comoving a t₀ s := by
    unfold lumDistFlat; rw [hzs]
  rw [hls] at hbs
  have hI : a t₀ * comoving a t₀ s * hubble a t₀
      = ∫ v in w..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
    have hw2p : 0 < w ^ 2 := by positivity
    field_simp at hbs
    linarith
  have hz0 : 0 < 1 + redshift a t₀ t := by unfold redshift; rw [add_sub_cancel]; positivity
  have key : a t₀ * comoving a t₀ s * hubble a t₀ ≤ a t₀ * comoving a t₀ t * hubble a t₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcom ha₀.le) hH₀.le
  have e : lumDistFlat a t₀ t * hubble a t₀ = (1 + redshift a t₀ t) * (a t₀ * comoving a t₀ t * hubble a t₀) := by
    unfold lumDistFlat; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) hz0.le

/-- The miss at redshift three from a lower bound `L` of `d_L H₀`. -/
theorem bk_z3_of (Ω : ℝ) (h2 : Ω ≤ 2 / 5) (a : ℝ → ℝ) (t t₀ : ℝ) (hH₀ : 0 < hubble a t₀)
    (hz : redshift a t₀ t = 3) (L : ℝ) (hL : L ≤ lumDistFlat a t₀ t * hubble a t₀)
    (hpoly : Qc Ω (2 * 0.6931471808) < L * (1 - 9 / 100 / 5 * (10 / 3 * 0.6931471808))) :
    0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
    9 / 100 < 5 * Real.logb 10
      (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) := by
  rw [poly_eq Ω _ _ hH₀.ne', hz, log4]
  set D := lumDistFlat a t₀ t
  set H := hubble a t₀
  have hu : 0 < 2 * Real.log 2 := by positivity
  have hQ := bk_Qc_pos Ω _ h2 hu
  have hQm := bk_Qc_mono Ω _ (2 * 0.6931471808) h2 hu.le (by linarith [Real.log_two_lt_d9])
  refine ⟨div_pos hQ hH₀, ?_⟩
  have hX : D / (Qc Ω (2 * Real.log 2) / H) = D * H / Qc Ω (2 * Real.log 2) := by field_simp
  rw [hX]
  have hκ : (0:ℝ) < 1 - 9 / 100 / 5 * (10 / 3 * 0.6931471808) := by norm_num
  have hL0 : 0 < L := by
    by_contra hc; push Not at hc; nlinarith
  have hDH : 0 < D * H := by linarith
  apply five_logb_gt _ _ (div_pos hDH hQ) (by norm_num)
  rw [div_mul_eq_mul_div, one_lt_div hQ]
  nlinarith

/-- The miss at redshift seven from a lower bound `L` of `d_L H₀`. -/
theorem bk_z7_of (Ω : ℝ) (h2 : Ω ≤ 2 / 5) (a : ℝ → ℝ) (t t₀ : ℝ) (hH₀ : 0 < hubble a t₀)
    (hz : redshift a t₀ t = 7) (L : ℝ) (hL : L ≤ lumDistFlat a t₀ t * hubble a t₀)
    (hpoly : Qc Ω (3 * 0.6931471808) < L * (1 - 3 / 10 / 5 * (10 / 3 * 0.6931471808))) :
    0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
    3 / 10 < 5 * Real.logb 10
      (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) := by
  rw [poly_eq Ω _ _ hH₀.ne', hz, log8]
  set D := lumDistFlat a t₀ t
  set H := hubble a t₀
  have hu : 0 < 3 * Real.log 2 := by positivity
  have hQ := bk_Qc_pos Ω _ h2 hu
  have hQm := bk_Qc_mono Ω _ (3 * 0.6931471808) h2 hu.le (by linarith [Real.log_two_lt_d9])
  refine ⟨div_pos hQ hH₀, ?_⟩
  have hX : D / (Qc Ω (3 * Real.log 2) / H) = D * H / Qc Ω (3 * Real.log 2) := by field_simp
  rw [hX]
  have hκ : (0:ℝ) < 1 - 3 / 10 / 5 * (10 / 3 * 0.6931471808) := by norm_num
  have hL0 : 0 < L := by
    by_contra hc; push Not at hc; nlinarith
  have hDH : 0 < D * H := by linarith
  apply five_logb_gt _ _ (div_pos hDH hQ) (by norm_num)
  rw [div_mul_eq_mul_div, one_lt_div hQ]
  nlinarith

/-- The difference of the two misses from an upper bound `U` of `d_L H₀` at redshift three and a lower
bound `L` at redshift seven. -/
theorem bk_shape_of (Ω : ℝ) (h2 : Ω ≤ 2 / 5) (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (hH₀ : 0 < hubble a t₀)
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7) (U L : ℝ)
    (h30 : 0 < lumDistFlat a t₀ t₃ * hubble a t₀)
    (hU : lumDistFlat a t₀ t₃ * hubble a t₀ ≤ U) (hL : L ≤ lumDistFlat a t₀ t₇ * hubble a t₀)
    (hpoly : U * Qc Ω (3 * 0.6931471808) <
      L * Qc Ω (2 * 0.6931471803) * (1 - 18 / 100 / 5 * (10 / 3 * 0.6931471808))) :
    18 / 100 < 5 * Real.logb 10
        (lumDistFlat a t₀ t₇ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₇))
      - 5 * Real.logb 10
        (lumDistFlat a t₀ t₃ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₃)) := by
  rw [poly_eq Ω _ (redshift a t₀ t₇) hH₀.ne', poly_eq Ω _ (redshift a t₀ t₃) hH₀.ne', hz₃, hz₇,
    log4, log8]
  set D3 := lumDistFlat a t₀ t₃
  set D7 := lumDistFlat a t₀ t₇
  set H := hubble a t₀
  set Q3 := Qc Ω (2 * Real.log 2)
  set Q7 := Qc Ω (3 * Real.log 2)
  have hQ3 : 0 < Q3 := bk_Qc_pos Ω _ h2 (by positivity)
  have hQ7 : 0 < Q7 := bk_Qc_pos Ω _ h2 (by positivity)
  have hQ7m : Q7 ≤ Qc Ω (3 * 0.6931471808) :=
    bk_Qc_mono Ω _ _ h2 (by positivity) (by linarith [Real.log_two_lt_d9])
  have hQ3m : Qc Ω (2 * 0.6931471803) ≤ Q3 :=
    bk_Qc_mono Ω _ _ h2 (by norm_num) (by linarith [Real.log_two_gt_d9])
  have hQ3l : 0 < Qc Ω (2 * 0.6931471803) := bk_Qc_pos Ω _ h2 (by norm_num)
  have hκ : (0:ℝ) < 1 - 18 / 100 / 5 * (10 / 3 * 0.6931471808) := by norm_num
  have hU0 : 0 < U := by linarith
  have hL0 : 0 < L := by
    by_contra hc; push Not at hc
    have : L * Qc Ω (2 * 0.6931471803) * (1 - 18 / 100 / 5 * (10 / 3 * 0.6931471808)) ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg hc hQ3l.le
      exact mul_nonpos_of_nonpos_of_nonneg this hκ.le
    have : 0 < U * Qc Ω (3 * 0.6931471808) := mul_pos hU0 (lt_of_lt_of_le hQ7 hQ7m)
    linarith
  have h70 : 0 < D7 * H := by linarith
  have hX7 : D7 / (Q7 / H) = D7 * H / Q7 := by field_simp
  have hX3 : D3 / (Q3 / H) = D3 * H / Q3 := by field_simp
  rw [hX7, hX3]
  have hX7p : 0 < D7 * H / Q7 := by positivity
  have hX3p : 0 < D3 * H / Q3 := by positivity
  rw [← mul_sub, ← Real.logb_div hX7p.ne' hX3p.ne']
  apply five_logb_gt _ _ (by positivity) (by norm_num)
  have hX : D7 * H / Q7 / (D3 * H / Q3) = (D7 * H) * Q3 / ((D3 * H) * Q7) := by field_simp
  rw [hX, div_mul_eq_mul_div, one_lt_div (by positivity)]
  have e1 : (D3 * H) * Q7 ≤ U * Qc Ω (3 * 0.6931471808) :=
    mul_le_mul hU hQ7m hQ7.le hU0.le
  have e2 : L * Qc Ω (2 * 0.6931471803) ≤ (D7 * H) * Q3 :=
    mul_le_mul hL hQ3m hQ3l.le h70.le
  have e3 := mul_le_mul_of_nonneg_right e2 hκ.le
  linarith

/-- `d_L H₀ = 4 J₃` at redshift three for `0 ≤ Ω ≤ 1`. -/
theorem bk_br3 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ1 : Ω ≤ 1) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz : redshift a t₀ t = 3) :
    lumDistFlat a t₀ t * hubble a t₀ = 4 * ∫ v in (1/2:ℝ)..1, gL Ω v := by
  have hbr := lumDistFlat_flatLCDM Ω hΩ₀ hΩ1 a t t₀ htt hpos hdiff hH₀ hH
  have hat : 0 < a t := hpos t ⟨le_rfl, htt⟩
  have hw : √(1 / (1 + 3) : ℝ) = 1 / 2 := by
    rw [show (1 / (1 + 3) : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [ratio_of_z a t t₀ 3 hat (hpos t₀ ⟨htt, le_rfl⟩) hz, hw, hz] at hbr
  change lumDistFlat a t₀ t = (1 + 3) / hubble a t₀ * ∫ v in (1/2:ℝ)..1, gL Ω v at hbr
  rw [hbr]; field_simp; ring

/-- `d_L H₀ = 8 J₇` at redshift seven for `0 ≤ Ω ≤ 1`. -/
theorem bk_br7 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ1 : Ω ≤ 1) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz : redshift a t₀ t = 7) :
    lumDistFlat a t₀ t * hubble a t₀ = 8 * ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v := by
  have hbr := lumDistFlat_flatLCDM Ω hΩ₀ hΩ1 a t t₀ htt hpos hdiff hH₀ hH
  have hat : 0 < a t := hpos t ⟨le_rfl, htt⟩
  rw [ratio_of_z a t t₀ 7 hat (hpos t₀ ⟨htt, le_rfl⟩) hz, hz] at hbr
  change lumDistFlat a t₀ t = (1 + 7) / hubble a t₀ * ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v at hbr
  rw [hbr]; field_simp; ring

theorem bk_a_of (a : ℝ → ℝ) (t t₀ z : ℝ) (ha : 0 < a t) (ha₀ : 0 < a t₀) (hz : redshift a t₀ t = z) :
    a t = a t₀ / (1 + z) := by
  have := ratio_of_z a t t₀ z ha ha₀ hz
  have h1 : 0 < 1 + z := by rw [← hz]; unfold redshift; rw [add_sub_cancel]; positivity
  field_simp at this ⊢; linarith

/-- The radicand of the law at the source, in terms of its redshift. -/
theorem bk_unreach (Ω : ℝ) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (z : ℝ) (hz : redshift a t₀ t = z) (hneg : Ω * (1 + z) ^ 3 + 1 - Ω < 0) : False :=
  bi_unreach Ω a t t₀ htt hpos hdiff hH (by rw [hz]; exact hneg)


/-- For a negative density reaching redshift seven, `d_L H₀ ≤ 4 · 33/10` at redshift three (the bridge from
the source and the comparison `bi_upper` above one half). -/
theorem bk_up3 (Ω : ℝ) (h0 : Ω < 0) (hn : 0 ≤ Ω * (1 + 7) ^ 3 + 1 - Ω) (a : ℝ → ℝ) (t₃ t₀ : ℝ)
    (h₃₀ : t₃ ≤ t₀) (hpos3 : ∀ s ∈ Set.Icc t₃ t₀, 0 < a s)
    (hdiff3 : ∀ s ∈ Set.Icc t₃ t₀, DifferentiableAt ℝ a s) (hH₀ : 0 < hubble a t₀)
    (hH3 : ∀ s ∈ Set.Icc t₃ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hat3 : a t₃ = a t₀ / (1 + 3)) :
    lumDistFlat a t₀ t₃ * hubble a t₀ ≤ 4 * (33 / 10) := by
    have ha₀ : 0 < a t₀ := hpos3 t₀ ⟨h₃₀, le_rfl⟩
    -- upper bound at redshift three: the bridge from the source and the comparison above one half
    have hR : 0 < Ω + (1 - Ω) * (1 / 2 : ℝ) ^ 6 := by nlinarith
    have h3w : √(a t₃ / a t₀) = 1 / 2 := by
      rw [hat3, show a t₀ / (1 + 3) / a t₀ = (1 / 2) ^ 2 by field_simp; norm_num]
      exact Real.sqrt_sq (by norm_num)
    have hb3 := bi_bridge Ω (by linarith) a t₃ t₀ h₃₀ hpos3 hdiff3 hH₀ hH3 (by rw [h3w]; exact hR)
    rw [h3w, hz₃] at hb3
    have hup := bi_upper Ω (1 / 2) h0.le (by norm_num) (by norm_num) hR
    have hsq : (1 / 8 : ℝ) * (10 / 11) ≤ √(Ω + (1 - Ω) * (1 / 2 : ℝ) ^ 6) := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    have hr : (1 / 2 : ℝ) ^ 3 / √(Ω + (1 - Ω) * (1 / 2 : ℝ) ^ 6) ≤ 11 / 10 := by
      rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hsq)]; nlinarith
    have hI : ∫ v in (1 / 2 : ℝ)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ 33 / 10 := by
      have h3 : (1:ℝ) / (1 / 2) ^ 2 - 1 / 1 ^ 2 = 3 := by norm_num
      rw [h3] at hup; nlinarith
    rw [hb3]; field_simp; nlinarith

/-- Without `1/5 ≤ Ω`: for `0 ≤ Ω < 1/5` certified enclosures on five density pieces, for a negative
density the empty-model comparison (or no model reaches the source). -/
theorem cubic_misses_z3_r1 : dropped% Checked.Cosmography.B1.cubic_misses_z3 1 := by
  intro Ω hΩ₂ a t t₀ htt hpos hdiff hH₀ hH hz
  rcases le_or_gt (1 / 5) Ω with h1 | h1
  · exact cubic_misses_z3 Ω h1 hΩ₂ a t t₀ htt hpos hdiff hH₀ hH hz
  rcases le_or_gt 0 Ω with h0 | h0
  · have hb := bk_br3 Ω h0 (by linarith) a t t₀ htt hpos hdiff hH₀ hH hz
    have go : ∀ A B : ℝ, A - B * Ω ≤ ∫ v in (1/2:ℝ)..1, gL Ω v →
        Qc Ω (2 * 0.6931471808) < 4 * (A - B * Ω) * (1 - 9 / 100 / 5 * (10 / 3 * 0.6931471808)) →
        0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
        9 / 100 < 5 * Real.logb 10
          (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) :=
      fun A B hJ hp => bk_z3_of Ω hΩ₂ a t t₀ hH₀ hz (4 * (A - B * Ω)) (by rw [hb]; linarith) hp
    rcases le_total Ω (1 / 50) with p0 | p0
    · exact go _ _ (bkJ3_lo0' Ω h0 (by linarith)) (bkz3_poly0 Ω h0 p0)
    rcases le_total Ω (1 / 20) with p1 | p1
    · exact go _ _ (bkJ3_lo1' Ω h0 (by linarith)) (bkz3_poly1 Ω p0 p1)
    rcases le_total Ω (1 / 10) with p2 | p2
    · exact go _ _ (bkJ3_lo2' Ω h0 (by linarith)) (bkz3_poly2 Ω p1 p2)
    rcases le_total Ω (3 / 20) with p3 | p3
    · exact go _ _ (bkJ3_lo3' Ω h0 (by linarith)) (bkz3_poly3 Ω p2 p3)
    · exact go _ _ (bkJ3_lo4' Ω h0 (by linarith)) (bkz3_poly4 Ω p3 h1.le)
  · have ha₀ : 0 < a t₀ := hpos t₀ ⟨htt, le_rfl⟩
    have hat := bk_a_of a t t₀ 3 (hpos t ⟨le_rfl, htt⟩) ha₀ hz
    rcases lt_or_ge (Ω * (1 + 3) ^ 3 + 1 - Ω) 0 with hn | hn
    · exact (bk_unreach Ω a t t₀ htt hpos hdiff hH 3 hz hn).elim
    have hf := bk_far Ω h0.le a t t₀ htt hpos hdiff hH₀ hH (5 / 9) (by norm_num) (by norm_num)
      (by rw [hat]; nlinarith) (by nlinarith)
    rw [hz] at hf
    apply bk_z3_of Ω hΩ₂ a t t₀ hH₀ hz _ hf
    unfold Qc
    nlinarith

theorem cubic_misses_z7_r1 : dropped% Checked.Cosmography.B1.cubic_misses_z7 1 := by
  intro Ω hΩ₂ a t t₀ htt hpos hdiff hH₀ hH hz
  rcases le_or_gt (1 / 5) Ω with h1 | h1
  · exact cubic_misses_z7 Ω h1 hΩ₂ a t t₀ htt hpos hdiff hH₀ hH hz
  rcases le_or_gt 0 Ω with h0 | h0
  · have hb := bk_br7 Ω h0 (by linarith) a t t₀ htt hpos hdiff hH₀ hH hz
    have go : ∀ A B : ℝ, A - B * Ω ≤ ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v →
        Qc Ω (3 * 0.6931471808) < 8 * (A - B * Ω) * (1 - 3 / 10 / 5 * (10 / 3 * 0.6931471808)) →
        0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
        3 / 10 < 5 * Real.logb 10
          (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) :=
      fun A B hJ hp => bk_z7_of Ω hΩ₂ a t t₀ hH₀ hz (8 * (A - B * Ω)) (by rw [hb]; linarith) hp
    rcases le_total Ω (1 / 50) with p0 | p0
    · exact go _ _ (bkJ7_lo0 Ω h0 (by linarith)) (bkz7_poly0 Ω h0 p0)
    rcases le_total Ω (1 / 20) with p1 | p1
    · exact go _ _ (bkJ7_lo1 Ω h0 (by linarith)) (bkz7_poly1 Ω p0 p1)
    rcases le_total Ω (1 / 10) with p2 | p2
    · exact go _ _ (bkJ7_lo2 Ω h0 (by linarith)) (bkz7_poly2 Ω p1 p2)
    rcases le_total Ω (3 / 20) with p3 | p3
    · exact go _ _ (bkJ7_lo3 Ω h0 (by linarith)) (bkz7_poly3 Ω p2 p3)
    · exact go _ _ (bkJ7_lo4 Ω h0 (by linarith)) (bkz7_poly4 Ω p3 h1.le)
  · have ha₀ : 0 < a t₀ := hpos t₀ ⟨htt, le_rfl⟩
    have hat := bk_a_of a t t₀ 7 (hpos t ⟨le_rfl, htt⟩) ha₀ hz
    rcases lt_or_ge (Ω * (1 + 7) ^ 3 + 1 - Ω) 0 with hn | hn
    · exact (bk_unreach Ω a t t₀ htt hpos hdiff hH 7 hz hn).elim
    have hf := bk_far Ω h0.le a t t₀ htt hpos hdiff hH₀ hH (9 / 25) (by norm_num) (by norm_num)
      (by rw [hat]; nlinarith) (by nlinarith)
    rw [hz] at hf
    apply bk_z7_of Ω hΩ₂ a t t₀ hH₀ hz _ hf
    unfold Qc
    nlinarith

theorem cubic_shape_miss_r1 : dropped% Checked.Cosmography.B1.cubic_shape_miss 1 := by
  intro Ω hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₇
  rcases le_or_gt (1 / 5) Ω with h1 | h1
  · exact cubic_shape_miss Ω h1 hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₇
  have h₇₀ : t₇ ≤ t₀ := le_trans h₇₃ h₃₀
  have hsub : Set.Icc t₃ t₀ ⊆ Set.Icc t₇ t₀ := Set.Icc_subset_Icc_left h₇₃
  have hpos3 : ∀ s ∈ Set.Icc t₃ t₀, 0 < a s := fun s hs => hpos s (hsub hs)
  have hdiff3 : ∀ s ∈ Set.Icc t₃ t₀, DifferentiableAt ℝ a s := fun s hs => hdiff s (hsub hs)
  have hH3 : ∀ s ∈ Set.Icc t₃ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω) := fun s hs => hH s (hsub hs)
  rcases le_or_gt 0 Ω with h0 | h0
  · have hb3 := bk_br3 Ω h0 (by linarith) a t₃ t₀ h₃₀ hpos3 hdiff3 hH₀ hH3 hz₃
    have hb7 := bk_br7 Ω h0 (by linarith) a t₇ t₀ h₇₀ hpos hdiff hH₀ hH hz₇
    have hJ3 := J3_lower0 Ω h0 (by linarith)
    have h30 : 0 < lumDistFlat a t₀ t₃ * hubble a t₀ := by rw [hb3]; linarith
    have go : ∀ A B C D : ℝ, A - B * Ω ≤ ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v →
        ∫ v in (1/2:ℝ)..1, gL Ω v ≤ C + D * Ω →
        4 * (C + D * Ω) * Qc Ω (3 * 0.6931471808) <
          8 * (A - B * Ω) * Qc Ω (2 * 0.6931471803) * (1 - 18 / 100 / 5 * (10 / 3 * 0.6931471808)) →
        18 / 100 < 5 * Real.logb 10
            (lumDistFlat a t₀ t₇ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₇))
          - 5 * Real.logb 10
            (lumDistFlat a t₀ t₃ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₃)) :=
      fun A B C D hl hu hp => bk_shape_of Ω hΩ₂ a t₇ t₃ t₀ hH₀ hz₃ hz₇ _ _ h30
        (by rw [hb3]; linarith) (by rw [hb7]; linarith) hp
    rcases le_total Ω (1 / 50) with p0 | p0
    · exact go _ _ _ _ (bkJ7_lo0 Ω h0 (by linarith)) (bkJ3_up0 Ω h0 p0) (bksh_poly0 Ω h0 p0)
    rcases le_total Ω (1 / 20) with p1 | p1
    · exact go _ _ _ _ (bkJ7_lo1 Ω h0 (by linarith)) (bkJ3_up1 Ω p0 p1) (bksh_poly1 Ω p0 p1)
    rcases le_total Ω (1 / 10) with p2 | p2
    · exact go _ _ _ _ (bkJ7_lo2 Ω h0 (by linarith)) (bkJ3_up2 Ω p1 p2) (bksh_poly2 Ω p1 p2)
    rcases le_total Ω (3 / 20) with p3 | p3
    · exact go _ _ _ _ (bkJ7_lo3 Ω h0 (by linarith)) (bkJ3_up3 Ω p2 p3) (bksh_poly3 Ω p2 p3)
    · exact go _ _ _ _ (bkJ7_lo4 Ω h0 (by linarith)) (bkJ3_up4 Ω p3 h1.le) (bksh_poly4 Ω p3 h1.le)
  · have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₇₀, le_rfl⟩
    have hat7 := bk_a_of a t₇ t₀ 7 (hpos t₇ ⟨le_rfl, h₇₀⟩) ha₀ hz₇
    have hat3 := bk_a_of a t₃ t₀ 3 (hpos t₃ ⟨h₇₃, h₃₀⟩) ha₀ hz₃
    rcases lt_or_ge (Ω * (1 + 7) ^ 3 + 1 - Ω) 0 with hn | hn
    · exact (bk_unreach Ω a t₇ t₀ h₇₀ hpos hdiff hH 7 hz₇ hn).elim
    have hf7 := bk_far Ω h0.le a t₇ t₀ h₇₀ hpos hdiff hH₀ hH (9 / 25) (by norm_num) (by norm_num)
      (by rw [hat7]; nlinarith) (by nlinarith)
    rw [hz₇] at hf7
    have hf3 := bk_far Ω h0.le a t₃ t₀ h₃₀ hpos3 hdiff3 hH₀ hH3 (1 / 2) (by norm_num) (by norm_num)
      (by rw [hat3]; nlinarith) (by nlinarith)
    rw [hz₃] at hf3
    have hU := bk_up3 Ω h0 hn a t₃ t₀ h₃₀ hpos3 hdiff3 hH₀ hH3 hz₃ hat3
    apply bk_shape_of Ω hΩ₂ a t₇ t₃ t₀ hH₀ hz₃ hz₇ _ _ (by linarith) hU hf7
    unfold Qc
    nlinarith

/-! ## Below the density one fifth: the separation -/

/-- `B1Sep.case_step` with the density bounded above only (the step uses the lower bound only through the
monotonicity of the ΛCDM polynomial, which holds for every density up to two fifths). -/
theorem bk_case (Ω a₂ a₃ J3 J7 L U ρ m : ℝ) (hΩ₂ : Ω ≤ 2 / 5)
    (hP3 : 0 < 2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
    (hmatch : 2 * J7 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) *
        (2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
      ≤ J3 * (3 * Real.log 2 + a₂ / Real.log 10 * (3 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2) ^ 3))
    (hJ3 : 0 < J3) (hL : L ≤ J7) (hU : J3 ≤ U) (hρ : 0 ≤ ρ)
    (hlin : ρ * U ≤ 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)))
    (hmq : m ≤ ρ * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808)) (hm : 0 < m)
    (hD : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4) < m ^ 2) :
    (5 / 4) ^ 2 < (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 := by
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  set P3 := 2 * ℓ + a₂ / l * (2 * ℓ) ^ 2 + a₃ / l ^ 2 * (2 * ℓ) ^ 3 with hP3def
  set P7 := 3 * ℓ + a₂ / l * (3 * ℓ) ^ 2 + a₃ / l ^ 2 * (3 * ℓ) ^ 3 with hP7def
  have hκ : 0 < 1 - 1 / 10 / 5 * (10 / 3 * (0.6931471808 : ℝ)) := by norm_num
  -- P₇ ≥ ρ P₃
  have h1 : ρ * J3 * P3 ≤ J3 * P7 := by
    have e1 : ρ * J3 * P3 ≤ ρ * U * P3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU hρ) hP3.le
    have e2 : ρ * U * P3 ≤ 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3 :=
      mul_le_mul_of_nonneg_right hlin hP3.le
    have e3 : 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3
        ≤ 2 * J7 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3 := by
      apply mul_le_mul_of_nonneg_right _ hP3.le
      exact mul_le_mul_of_nonneg_right (by linarith) hκ.le
    linarith
  have h2 : ρ * P3 ≤ P7 := by
    have : J3 * (ρ * P3) ≤ J3 * P7 := by linarith
    exact le_of_mul_le_mul_left this hJ3
  -- expand around the ΛCDM point
  have hQ2 : Qc Ω (2 * 0.6931471803) ≤ Qc Ω (2 * ℓ) :=
    bk_Qc_mono Ω _ _ hΩ₂ (by norm_num) (by linarith [Real.log_two_gt_d9])
  have hQ3 : Qc Ω (3 * ℓ) ≤ Qc Ω (3 * 0.6931471808) :=
    bk_Qc_mono Ω _ _ hΩ₂ (by positivity) (by linarith [Real.log_two_lt_d9])
  set d₂ := a₂ / l - (3 / 2 - 3 / 4 * Ω) with hd₂
  set d₃ := a₃ / l ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6) with hd₃
  have hexp : P7 - ρ * P3 = Qc Ω (3 * ℓ) - ρ * Qc Ω (2 * ℓ)
      + (d₂ * ((9 - 4 * ρ) * ℓ ^ 2) + d₃ * ((27 - 8 * ρ) * ℓ ^ 3)) := by
    rw [hP7def, hP3def, hd₂, hd₃]; unfold Qc; ring
  have hρQ : ρ * Qc Ω (2 * 0.6931471803) ≤ ρ * Qc Ω (2 * ℓ) := mul_le_mul_of_nonneg_left hQ2 hρ
  have hlin2 : m ≤ d₂ * ((9 - 4 * ρ) * ℓ ^ 2) + d₃ * ((27 - 8 * ρ) * ℓ ^ 3) := by linarith
  have hc := core (5 / 4) ρ m ℓ l d₂ d₃ log_ten_ge hℓ0 (by linarith [Real.log_two_lt_d9]) hm hlin2 hD
  have e2 : l * d₂ = a₂ - lusA2 Ω := by rw [hd₂]; unfold lusA2; field_simp; ring
  have e3 : l ^ 2 * d₃ = a₃ - lusA3 Ω := by rw [hd₃]; unfold lusA3; field_simp; ring
  rwa [e2, e3] at hc


/-- The matching inequality of `B1Sep.matching` in terms of `d_L H₀` at the two sources. -/
theorem bk_match (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ)
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H) (h3 : 0 < lumDistFlat a t₀ t₃) (h7 : 0 < lumDistFlat a t₀ t₇)
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₇ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇))
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₇ : |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₇)) - c|
      ≤ 1 / 20) (H₀ : ℝ) (hH₀ : 0 < H₀) :
    0 < 2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
        + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3 ∧
    2 * (lumDistFlat a t₀ t₇ * H₀ / 8) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) *
        (2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
      ≤ (lumDistFlat a t₀ t₃ * H₀ / 4) * (3 * Real.log 2 + a₂ / Real.log 10 * (3 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2) ^ 3) := by
  rw [poly_gen a₂ a₃ H _ hHp.ne', hz₃, log4] at hp₃ hm₃
  rw [poly_gen a₂ a₃ H _ hHp.ne', hz₇, log8] at hp₇ hm₇
  set D3 := lumDistFlat a t₀ t₃
  set D7 := lumDistFlat a t₀ t₇
  set P3 := 2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3 with hP3def
  set P7 := 3 * Real.log 2 + a₂ / Real.log 10 * (3 * Real.log 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2) ^ 3 with hP7def
  have hP3 : 0 < P3 := by
    have := hp₃; rw [div_pos_iff_of_pos_right hHp] at this; exact this
  have hP7 : 0 < P7 := by
    have := hp₇; rw [div_pos_iff_of_pos_right hHp] at this; exact this
  set X3 := D3 / (P3 / H) with hX3
  set X7 := D7 / (P7 / H) with hX7
  have hX3p : 0 < X3 := by positivity
  have hX7p : 0 < X7 := by positivity
  have hdiffm : 5 * Real.logb 10 (X7 / X3) ≤ 1 / 10 := by
    rw [Real.logb_div hX7p.ne' hX3p.ne']
    have h3' := abs_le.1 hm₃
    have h7' := abs_le.1 hm₇
    linarith
  have hY : X7 / X3 = 2 * (D7 * H₀ / 8) * P3 / ((D3 * H₀ / 4) * P7) := by
    rw [hX7, hX3]; field_simp; ring
  have hκ : X7 / X3 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) ≤ 1 := by
    by_contra hc
    push Not at hc
    have := five_logb_gt (1 / 10) (X7 / X3) (by positivity) (by norm_num) hc
    linarith
  rw [hY] at hκ
  refine ⟨hP3, ?_⟩
  have hpos' : 0 < (D3 * H₀ / 4) * P7 := by positivity
  rw [div_mul_eq_mul_div, div_le_one hpos'] at hκ
  linarith

theorem bksep_lin0 (Ω : ℝ) (ha : (0 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 50 : ℝ)) :
    (74 / 25 : ℝ) * ((9512683 / 3125000 : ℝ) + (-534133689 / 25000000 : ℝ) * Ω) ≤ 2 * ((289202889 / 50000000 : ℝ) - (538616373 / 6250000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  linarith

theorem bksep_mq0 (Ω : ℝ) (ha : (0 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 50 : ℝ)) :
    (1738 / 625 : ℝ) ≤ (74 / 25 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksep_dd0 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (74 / 25 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (74 / 25 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (1738 / 625 : ℝ) ^ 2 := by norm_num

theorem bksep_lin1 (Ω : ℝ) (ha : (1 / 50 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 20 : ℝ)) :
    (5631 / 2000 : ℝ) * ((28349403 / 10000000 : ℝ) + (-1090978663 / 100000000 : ℝ) * Ω) ≤ 2 * ((470513689 / 100000000 : ℝ) - (2651922687 / 100000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  linarith

theorem bksep_mq1 (Ω : ℝ) (ha : (1 / 50 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 20 : ℝ)) :
    (8787 / 5000 : ℝ) ≤ (5631 / 2000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksep_dd1 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (5631 / 2000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (5631 / 2000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (8787 / 5000 : ℝ) ^ 2 := by norm_num

theorem bksep_lin2 (Ω : ℝ) (ha : (1 / 20 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 10 : ℝ)) :
    (26819 / 10000 : ℝ) * ((25900867 / 10000000 : ℝ) + (-601270449 / 100000000 : ℝ) * Ω) ≤ 2 * ((79203409 / 20000000 : ℝ) - (1164058961 / 100000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  linarith

theorem bksep_mq2 (Ω : ℝ) (ha : (1 / 20 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 10 : ℝ)) :
    (351 / 400 : ℝ) ≤ (26819 / 10000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksep_dd2 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (26819 / 10000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (26819 / 10000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (351 / 400 : ℝ) ^ 2 := by norm_num

theorem bksep_lin3 (Ω : ℝ) (ha : (1 / 10 : ℝ) ≤ Ω) (hb : Ω ≤ (3 / 20 : ℝ)) :
    (13189 / 5000 : ℝ) * ((2949157 / 1250000 : ℝ) + (-370510573 / 100000000 : ℝ) * Ω) ≤ 2 * ((346770341 / 100000000 : ℝ) - (324577759 / 50000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  linarith

theorem bksep_mq3 (Ω : ℝ) (ha : (1 / 10 : ℝ) ≤ Ω) (hb : Ω ≤ (3 / 20 : ℝ)) :
    (3593 / 5000 : ℝ) ≤ (13189 / 5000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksep_dd3 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (13189 / 5000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (13189 / 5000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (3593 / 5000 : ℝ) ^ 2 := by norm_num

theorem bksep_lin4 (Ω : ℝ) (ha : (3 / 20 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 5 : ℝ)) :
    (13019 / 5000 : ℝ) * ((219914277 / 100000000 : ℝ) + (-32965389 / 12500000 : ℝ) * Ω) ≤ 2 * ((315528157 / 100000000 : ℝ) - (87339413 / 20000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  linarith

theorem bksep_mq4 (Ω : ℝ) (ha : (3 / 20 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 5 : ℝ)) :
    (6409 / 10000 : ℝ) ≤ (13019 / 5000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksep_dd4 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (13019 / 5000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (13019 / 5000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (6409 / 10000 : ℝ) ^ 2 := by norm_num

theorem bksep_linn (Ω : ℝ) (ha : (-1 / 511 : ℝ) ≤ Ω) (hb : Ω ≤ (0 : ℝ)) :
    (19411 / 5000 : ℝ) * ((33 / 10 : ℝ)) ≤ 2 * ((544 / 81 : ℝ)) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  linarith

theorem bksep_mqn (Ω : ℝ) (ha : (-1 / 511 : ℝ) ≤ Ω) (hb : Ω ≤ (0 : ℝ)) :
    (1198 / 125 : ℝ) ≤ (19411 / 5000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksep_ddn : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (19411 / 5000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (19411 / 5000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (1198 / 125 : ℝ) ^ 2 := by norm_num


/-- Without `1/5 ≤ Ω`: the separation from the same enclosures (densities in `[0, 1/5)`) and the
empty-model comparisons (negative densities). -/
theorem cubic_separation_r1 : dropped% Checked.Cosmography.B1Sep.cubic_separation 1 := by
  intro Ω hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₇ a₂ a₃ H c hHp hp₃ hp₇ hm₃ hm₇
  rcases le_or_gt (1 / 5) Ω with h1 | h1
  · exact cubic_separation Ω h1 hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₇ a₂ a₃ H c hHp
      hp₃ hp₇ hm₃ hm₇
  have h₇₀ : t₇ ≤ t₀ := le_trans h₇₃ h₃₀
  have hsub : Set.Icc t₃ t₀ ⊆ Set.Icc t₇ t₀ := Set.Icc_subset_Icc_left h₇₃
  have hpos3 : ∀ s ∈ Set.Icc t₃ t₀, 0 < a s := fun s hs => hpos s (hsub hs)
  have hdiff3 : ∀ s ∈ Set.Icc t₃ t₀, DifferentiableAt ℝ a s := fun s hs => hdiff s (hsub hs)
  have hH3 : ∀ s ∈ Set.Icc t₃ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω) := fun s hs => hH s (hsub hs)
  -- the step common to both ranges: bounds `L ≤ d_L H₀ / 8` at seven, `0 < d_L H₀ / 4 ≤ U` at three
  have fin : ∀ L U ρ m : ℝ, 0 < lumDistFlat a t₀ t₃ * hubble a t₀ →
      L ≤ lumDistFlat a t₀ t₇ * hubble a t₀ / 8 → lumDistFlat a t₀ t₃ * hubble a t₀ / 4 ≤ U →
      0 < ρ → ρ * U ≤ 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) →
      m ≤ ρ * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) → 0 < m →
      (5 / 4 : ℝ) ^ 2 * ((9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4) < m ^ 2 →
      (5 / 4) ^ 2 < (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 := by
    intro L U ρ m h30 hL hU hρ hlin hmq hm hD
    have hU0 : 0 < U := by linarith
    have hL0 : 0 < L := by
      have : 0 < ρ * U := mul_pos hρ hU0
      have hκ : (0:ℝ) < 1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808) := by norm_num
      by_contra hc; push Not at hc
      have : 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hκ.le
      linarith
    have h3 : 0 < lumDistFlat a t₀ t₃ := pos_of_mul_pos_left h30 hH₀.le
    have h7 : 0 < lumDistFlat a t₀ t₇ := pos_of_mul_pos_left (by linarith) hH₀.le
    obtain ⟨hP3, hmatch⟩ := bk_match a t₇ t₃ t₀ hz₃ hz₇ a₂ a₃ H c hHp h3 h7 hp₃ hp₇ hm₃ hm₇
      (hubble a t₀) hH₀
    exact bk_case Ω a₂ a₃ _ _ L U ρ m hΩ₂ hP3 hmatch (by linarith) hL hU hρ.le hlin hmq hm hD
  rcases le_or_gt 0 Ω with h0 | h0
  · have hb3 := bk_br3 Ω h0 (by linarith) a t₃ t₀ h₃₀ hpos3 hdiff3 hH₀ hH3 hz₃
    have hb7 := bk_br7 Ω h0 (by linarith) a t₇ t₀ h₇₀ hpos hdiff hH₀ hH hz₇
    have hJ3 := J3_lower0 Ω h0 (by linarith)
    have h30 : 0 < lumDistFlat a t₀ t₃ * hubble a t₀ := by rw [hb3]; linarith
    have go : ∀ A B C D ρ m : ℝ, A - B * Ω ≤ ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v →
        ∫ v in (1/2:ℝ)..1, gL Ω v ≤ C + D * Ω → 0 < ρ →
        ρ * (C + D * Ω) ≤ 2 * (A - B * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) →
        m ≤ ρ * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) → 0 < m →
        (5 / 4 : ℝ) ^ 2 * ((9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 /
          ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
        + (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4) < m ^ 2 →
        (5 / 4) ^ 2 < (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 :=
      fun A B C D ρ m hl hu hρ hlin hmq hm hD => fin _ _ ρ m h30 (by rw [hb7]; linarith)
        (by rw [hb3]; linarith) hρ hlin hmq hm hD
    rcases le_total Ω (1 / 50) with p0 | p0
    · exact go _ _ _ _ _ _ (bkJ7_lo0 Ω h0 (by linarith)) (bkJ3_up0 Ω h0 p0) (by norm_num)
        (bksep_lin0 Ω h0 p0) (bksep_mq0 Ω h0 p0) (by norm_num) bksep_dd0
    rcases le_total Ω (1 / 20) with p1 | p1
    · exact go _ _ _ _ _ _ (bkJ7_lo1 Ω h0 (by linarith)) (bkJ3_up1 Ω p0 p1) (by norm_num)
        (bksep_lin1 Ω p0 p1) (bksep_mq1 Ω p0 p1) (by norm_num) bksep_dd1
    rcases le_total Ω (1 / 10) with p2 | p2
    · exact go _ _ _ _ _ _ (bkJ7_lo2 Ω h0 (by linarith)) (bkJ3_up2 Ω p1 p2) (by norm_num)
        (bksep_lin2 Ω p1 p2) (bksep_mq2 Ω p1 p2) (by norm_num) bksep_dd2
    rcases le_total Ω (3 / 20) with p3 | p3
    · exact go _ _ _ _ _ _ (bkJ7_lo3 Ω h0 (by linarith)) (bkJ3_up3 Ω p2 p3) (by norm_num)
        (bksep_lin3 Ω p2 p3) (bksep_mq3 Ω p2 p3) (by norm_num) bksep_dd3
    · exact go _ _ _ _ _ _ (bkJ7_lo4 Ω h0 (by linarith)) (bkJ3_up4 Ω p3 h1.le) (by norm_num)
        (bksep_lin4 Ω p3 h1.le) (bksep_mq4 Ω p3 h1.le) (by norm_num) bksep_dd4
  · have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₇₀, le_rfl⟩
    have hat7 := bk_a_of a t₇ t₀ 7 (hpos t₇ ⟨le_rfl, h₇₀⟩) ha₀ hz₇
    have hat3 := bk_a_of a t₃ t₀ 3 (hpos t₃ ⟨h₇₃, h₃₀⟩) ha₀ hz₃
    rcases lt_or_ge (Ω * (1 + 7) ^ 3 + 1 - Ω) 0 with hn | hn
    · exact (bk_unreach Ω a t₇ t₀ h₇₀ hpos hdiff hH 7 hz₇ hn).elim
    have hf7 := bk_far Ω h0.le a t₇ t₀ h₇₀ hpos hdiff hH₀ hH (9 / 25) (by norm_num) (by norm_num)
      (by rw [hat7]; nlinarith) (by nlinarith)
    rw [hz₇] at hf7
    have hf3 := bk_far Ω h0.le a t₃ t₀ h₃₀ hpos3 hdiff3 hH₀ hH3 (1 / 2) (by norm_num) (by norm_num)
      (by rw [hat3]; nlinarith) (by nlinarith)
    rw [hz₃] at hf3
    have hU := bk_up3 Ω h0 hn a t₃ t₀ h₃₀ hpos3 hdiff3 hH₀ hH3 hz₃ hat3
    have hmin : (-1 / 511 : ℝ) ≤ Ω := by nlinarith
    exact fin (544 / 81) (33 / 10) _ _ (by linarith) (by linarith) (by linarith) (by norm_num)
      (bksep_linn Ω hmin h0.le) (bksep_mqn Ω hmin h0.le) (by norm_num) bksep_ddn

end Checked.Trust.NCBK
