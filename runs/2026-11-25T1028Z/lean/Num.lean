import Checked.Math.GelfandRatioCore
import Mathlib.Analysis.Real.Pi.Bounds
import Checked.Math.GSeg

namespace Checked.Math.GelfandRadiiCore
open Set Filter Topology

theorem gr_sqrt7 : (2.64575 : ℝ) ≤ Real.sqrt 7 ∧ Real.sqrt 7 ≤ 2.6458 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem gr_exp_lo1 : (10.3 : ℝ) ≤ Real.exp 2.3355 := by
  have := Real.sum_le_exp_of_nonneg (x := (2.3355 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

theorem gr_exp_hi1 : Real.exp 2.4154 ≤ 11.2 := by
  have := Checked.Math.GSeg.exp_le_pow4 (x := (2.4154 : ℝ)) (by norm_num) (by norm_num) 6 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

theorem gr_exp_lo2 : (0.28 : ℝ) ≤ Real.exp (-1.268) := by
  have := Checked.Math.GSeg.exp_le_pow4 (x := (1.268 : ℝ)) (by norm_num) (by norm_num) 6 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  linarith

theorem gr_exp_hi2 : Real.exp (-1.1094) ≤ 0.33 := by
  have := Real.sum_le_exp_of_nonneg (x := (1.1094 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- The four segment bounds with an error at most `1386 / 1000000` give the two quotient intervals. -/
theorem gr_num {ε L D : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1386 / 1000000)
    (h1 : (Real.sqrt 7 / 2 - 16 * ε) * L ≤ Real.pi)
    (h2 : Real.pi ≤ (Real.sqrt 7 / 2 + 16 * ε) * L)
    (h3 : -(1 + 36 * ε) * L ≤ D) (h4 : D ≤ -(1 - 36 * ε) * L) :
    10.3 ≤ Real.exp L ∧ Real.exp L ≤ 11.2 ∧ -0.33 ≤ -Real.exp (D / 2) ∧ -Real.exp (D / 2) ≤ -0.28 := by
  obtain ⟨s1, s2⟩ := gr_sqrt7
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have Lpos : 0 < L := by
    by_contra hL
    push Not at hL
    have : (Real.sqrt 7 / 2 + 16 * ε) * L ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hL
    linarith
  have Llo : 2.3355 ≤ L := by
    have : (1.345076 - (Real.sqrt 7 / 2 + 16 * ε)) * L ≥ 0 :=
      mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Lhi : L ≤ 2.4154 := by
    have : ((Real.sqrt 7 / 2 - 16 * ε) - 1.300699) * L ≥ 0 :=
      mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Dlo : -1.268 ≤ D / 2 := by
    have : (1.049896 - (1 + 36 * ε)) * L ≥ 0 := mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Dhi : D / 2 ≤ -1.1094 := by
    have : ((1 - 36 * ε) - 0.950104) * L ≥ 0 := mul_nonneg (by linarith) Lpos.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans gr_exp_lo1 (Real.exp_le_exp.2 Llo)
  · exact le_trans (Real.exp_le_exp.2 Lhi) gr_exp_hi1
  · have := le_trans (Real.exp_le_exp.2 Dhi) gr_exp_hi2; linarith
  · have := le_trans gr_exp_lo2 (Real.exp_le_exp.2 Dlo); linarith

/-- The first two segment bounds alone, with errors tending to zero, give the limit of the advance of log s
(the first half of `Checked.Math.GelfandRatioCore.lim_D`). -/
theorem lim_L {ε L : ℕ → ℝ} {K : ℕ} (hε : Tendsto ε atTop (𝓝 0))
    (h1 : ∀ k, K ≤ k → (Real.sqrt 7 / 2 - 16 * ε k) * L k ≤ Real.pi)
    (h2 : ∀ k, K ≤ k → Real.pi ≤ (Real.sqrt 7 / 2 + 16 * ε k) * L k) :
    Tendsto L atTop (𝓝 (Real.pi / (Real.sqrt 7 / 2))) := by
  set c := Real.sqrt 7 / 2 with hc
  have cpos : 0 < c := by positivity
  have hsmall : ∀ᶠ k in atTop, K ≤ k ∧ 16 * ε k < c / 2 ∧ -(c / 32) < ε k := by
    have e1 : ∀ᶠ k in atTop, 16 * ε k < c / 2 := by
      have : Tendsto (fun k => 16 * ε k) atTop (𝓝 (16 * 0)) := hε.const_mul 16
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    have e3 : ∀ᶠ k in atTop, -(c / 32) < ε k := hε.eventually (lt_mem_nhds (by linarith))
    filter_upwards [eventually_ge_atTop K, e1, e3] with k a b d using ⟨a, b, d⟩
  have hLlo : Tendsto (fun k => Real.pi / (c + 16 * ε k)) atTop (𝓝 (Real.pi / c)) := by
    have : Tendsto (fun k => c + 16 * ε k) atTop (𝓝 (c + 16 * 0)) := (hε.const_mul 16).const_add c
    rw [mul_zero, add_zero] at this
    exact tendsto_const_nhds.div this cpos.ne'
  have hLhi : Tendsto (fun k => Real.pi / (c - 16 * ε k)) atTop (𝓝 (Real.pi / c)) := by
    have : Tendsto (fun k => c - 16 * ε k) atTop (𝓝 (c - 16 * 0)) := (hε.const_mul 16).const_sub c
    rw [mul_zero, sub_zero] at this
    exact tendsto_const_nhds.div this cpos.ne'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLlo hLhi ?_ ?_
  · filter_upwards [hsmall] with k hk'
    obtain ⟨hk, a, a3⟩ := hk'
    have hp : 0 < c + 16 * ε k := by linarith
    rw [div_le_iff₀ hp]; linarith [h2 k hk]
  · filter_upwards [hsmall] with k hk'
    obtain ⟨hk, a, a3⟩ := hk'
    have hp : 0 < c - 16 * ε k := by linarith
    rw [le_div_iff₀ hp]; linarith [h1 k hk]

end Checked.Math.GelfandRadiiCore
