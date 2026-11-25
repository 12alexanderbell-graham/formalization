import Checked.Math.GelfandRatioCore
import Checked.Math.GelfandLam6Pos
import Mathlib.Analysis.Real.Pi.Bounds
import Checked.Math.GSeg

/-! Gelfand problem in the three-dimensional ball, `GelfandRadiiCore`: route of `Checked.Math.GelfandTurningRadii.gelfand_turning_radii` (run 2026-11-25T1028Z). The first two segment bounds of `Checked.Math.GelfandRatioCore.Sys.seg_bounds` squeeze the advance of log s between consecutive turning points (`lim_L`), and the quotient of the radii is its exponential. From the seventh turning point on, which lies beyond the start of the small ball by `Checked.Math.GelfandLam6Pos.zeta6_ge`, the weighted norm at every later turning point is at most its value there (`Sys.sqrtN_le`), which the branch parameter at that turning point bounds through `Checked.Math.GelfandLam6.lam3456_band` (the norm is eight times the square of half the deviation); `gr_num` turns the four segment bounds with that error into the two intervals by bounds on pi, the square root of seven and partial sums of the exponential series. -/

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
namespace Checked.Math.GelfandRadiiCore
open Set Filter Topology
open Checked.Math.GelfandRatioCore
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (lam U V Hyp hyp_of U_deriv V_deriv lam_deriv lam_eq_UV phi_neg)

theorem radii_main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      4.071496844 ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      3.321992118 ≤ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ∧ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ≤ 3.321992119 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ζ 0 → s ^ 2 * Real.exp (w s) < ζ 0 ^ 2 * Real.exp (w (ζ 0))) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k)), s ≠ ζ (2 * k + 1) →
        ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < s ^ 2 * Real.exp (w s)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k + 1)), s ≠ ζ (2 * k + 2) →
        s ^ 2 * Real.exp (w s) < ζ (2 * k + 2) ^ 2 * Real.exp (w (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < 2 ∧
        2 < ζ (2 * k) ^ 2 * Real.exp (w (ζ (2 * k)))) ∧
      Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 2) ∧
      StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ,
        StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      Tendsto (fun k : ℕ => (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) /
        (ζ k ^ 2 * Real.exp (w (ζ k)) - 2)) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) ∧
      Tendsto (fun k : ℕ => ζ (k + 1) / ζ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      (∀ k : ℕ, 6 ≤ k →
        10.3 ≤ ζ (k + 1) / ζ k ∧ ζ (k + 1) / ζ k ≤ 11.2 ∧
        -0.33 ≤ (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) ∧
        (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) ≤ -0.28) := by
  obtain ⟨ζ, hm, hT, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono⟩ :=
    Checked.Math.GelfandExtremaMain.main w φ hw hφ0 hφ h0
  refine ⟨ζ, hm, hT, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, ?_⟩
  have z6 := Checked.Math.GelfandLam6Pos.zeta6_ge w φ hw hφ0 hφ h0 ζ hm hz0lo hz0hi hinc0 hanti hmono
  have l6 := (Checked.Math.GelfandLam6.lam3456_band w φ hw hφ0 hφ h0 ζ hm hz0lo hz0hi hinc0 hanti hmono).2.2.2
  have E := hyp_of hw hφ0 hφ
  obtain ⟨r1, r2, r3⟩ := Checked.Math.BEAllMain.restrict 300000 hw hφ0 hφ
  obtain ⟨-, su, sv, -⟩ := Checked.Math.BEState300.state300 300000 le_rfl w φ r1 r2 r3 h0
  obtain ⟨N0le, N0pos⟩ := Checked.Math.BEAllMain.N0_bounds su sv
  have S : Sys (U w φ) (V φ) 300000 :=
    ⟨by norm_num, fun t ht => U_deriv E (by linarith [mem_Ici.1 ht]),
      fun t ht => V_deriv E (by linarith [mem_Ici.1 ht]), le_trans N0le (by norm_num), N0pos⟩
  have ζpos : ∀ n, 0 < ζ n := fun n =>
    lt_of_lt_of_le (by norm_num at hz0lo; linarith) (hm.monotone (Nat.zero_le n))
  -- the turning points are zeros of V − 2
  have hVz : ∀ n, V φ (ζ n) = 2 := by
    intro n
    apply V_two_of_extr E (ζpos n)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases m with _ | j
      · right
        filter_upwards [Ici_mem_nhds (ζpos 0)] with s hs
        by_cases h : s = ζ 0
        · rw [h]
        · exact (hmax0 s hs h).le
      · right
        have e : 2 * (j + 1) = 2 * j + 2 := by ring
        rw [e]
        filter_upwards [Ici_mem_nhds (hm (show 2 * j + 1 < 2 * j + 2 by omega))] with s hs
        by_cases h : s = ζ (2 * j + 2)
        · rw [h]
        · exact (hmax j s hs h).le
    · left
      filter_upwards [Ici_mem_nhds (hm (show 2 * m < 2 * m + 1 by omega))] with s hs
      by_cases h : s = ζ (2 * m + 1)
      · rw [h]
      · exact (hmin m s hs h).le
  -- from some index on, the turning points lie beyond 300000
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = 6 := ⟨6, rfl⟩
  have hKi : ∀ k, K ≤ k → ζ k ∈ Ici (300000 : ℝ) := fun k hk =>
    mem_Ici.2 (le_trans z6 (hm.monotone (hKdef ▸ hk)))
  -- the side of each segment
  have side : ∀ k, K ≤ k → ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ t ∈ Ioo (ζ k) (ζ (k + 1)), 0 < σ * (V φ t - 2) := by
    intro k hk
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · exact ⟨1, by norm_num, pos_of_anti E S (hKi _ hk) (hanti m)⟩
    · exact ⟨-1, by norm_num, neg_of_mono E S (hKi _ hk) (hmono m)⟩
  have B : ∀ k, K ≤ k →
      (Real.sqrt 7 / 2 - 16 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
        (Real.log (ζ (k + 1)) - Real.log (ζ k)) ≤ Real.pi ∧
      Real.pi ≤ (Real.sqrt 7 / 2 + 16 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
        (Real.log (ζ (k + 1)) - Real.log (ζ k)) ∧
      -(1 + 36 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
          (Real.log (ζ (k + 1)) - Real.log (ζ k)) ≤
        Real.log (Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2)) -
          Real.log (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) ∧
      Real.log (Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2)) -
          Real.log (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) ≤
        -(1 - 36 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
          (Real.log (ζ (k + 1)) - Real.log (ζ k)) := fun k hk => by
    obtain ⟨σ, hσ, hsg⟩ := side k hk
    exact Checked.Math.GelfandRatioCore.Sys.seg_bounds S hσ (hKi k hk) (hm (Nat.lt_succ_self k)) (hVz k) (hVz (k + 1)) hsg
  set ε : ℕ → ℝ := fun k => Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) with hεdef
  set L : ℕ → ℝ := fun k => Real.log (ζ (k + 1)) - Real.log (ζ k) with hLdef
  set D : ℕ → ℝ := fun k => Real.log (Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2)) -
    Real.log (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) with hDdef
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (S.N_tendsto.comp hT)
    rw [Real.sqrt_zero] at this
    exact this
  have hD := lim_D (ε := ε) (L := L) (D := D) (K := K) hε (fun k hk => (B k hk).1)
    (fun k hk => (B k hk).2.1) (fun k hk => (B k hk).2.2.1) (fun k hk => (B k hk).2.2.2)
  -- the quotient at the turning points
  have lam2 : ∀ n, ζ n ^ 2 * Real.exp (w (ζ n)) - 2 = 2 * (U w φ (ζ n) - 1) := by
    intro n
    have := lam_eq_UV E (ζpos n)
    unfold lam at this
    rw [this, hVz n]; ring
  have Nz : ∀ n, Nw (U w φ (ζ n) - 1) (V φ (ζ n) - 2) = 8 * (U w φ (ζ n) - 1) ^ 2 := by
    intro n; rw [hVz n]; unfold Nw; ring
  have alt : ∀ n, (ζ (n + 1) ^ 2 * Real.exp (w (ζ (n + 1))) - 2) *
      (ζ n ^ 2 * Real.exp (w (ζ n)) - 2) < 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have a1 := (h2 m).1
      have a2 := (h2 m).2
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · have a1 := (h2 m).1
      have a2 := (h2 (m + 1)).2
      have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [e] at a2
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hq : ∀ k, K ≤ k → (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) /
      (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) = -Real.exp (D k / 2) := by
    intro k _
    rw [lam2 (k + 1), lam2 k]
    have hs : (U w φ (ζ (k + 1)) - 1) * (U w φ (ζ k) - 1) < 0 := by
      have := alt k; rw [lam2 (k + 1), lam2 k] at this; nlinarith
    rw [show 2 * (U w φ (ζ (k + 1)) - 1) / (2 * (U w φ (ζ k) - 1)) =
      (U w φ (ζ (k + 1)) - 1) / (U w φ (ζ k) - 1) by
        rw [mul_div_mul_left _ _ two_ne_zero]]
    exact q_eq (Nz k) (Nz (k + 1)) hs
  have hL := lim_L (ε := ε) (L := L) (K := K) hε (fun k hk => (B k hk).1) (fun k hk => (B k hk).2.1)
  have hratio : ∀ k, ζ (k + 1) / ζ k = Real.exp (L k) := by
    intro k
    simp only [hLdef]
    rw [Real.exp_sub, Real.exp_log (ζpos _), Real.exp_log (ζpos _)]
  -- the error at the seventh turning point bounds every later one
  have e6 : ε K ≤ 1386 / 1000000 := by
    simp only [hεdef, hKdef]
    rw [Nz 6]
    have hx : 0 < U w φ (ζ K) - 1 := by
      have := (h2 3).2
      have e := lam2 6
      norm_num at this e
      linarith
    have hx' : U w φ (ζ K) - 1 ≤ 49 / 100000 := by
      have e := lam2 6
      norm_num at e l6
      linarith [l6.2]
    rw [show (1386 / 1000000 : ℝ) = Real.sqrt ((1386 / 1000000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have eK : ∀ k, K ≤ k → ε k ≤ 1386 / 1000000 := fun k hk =>
    le_trans (Sys.sqrtN_le S (hKi K le_rfl) (hm.monotone hk)) e6
  refine ⟨lim_q hD hq, ?_, ?_⟩
  · have := ((Real.continuous_exp.tendsto _).comp hL)
    have e : Real.pi / (Real.sqrt 7 / 2) = 2 * Real.pi / Real.sqrt 7 := by
      have : Real.sqrt 7 ≠ 0 := by positivity
      field_simp
    rw [e] at this
    refine this.congr' (Eventually.of_forall fun k => ?_)
    exact (hratio k).symm
  · intro k hk
    have nb := gr_num (Real.sqrt_nonneg _) (eK k hk) (B k hk).1 (B k hk).2.1 (B k hk).2.2.1 (B k hk).2.2.2
    rw [hratio k, hq k hk]
    exact nb
end Checked.Math.GelfandRadiiCore
