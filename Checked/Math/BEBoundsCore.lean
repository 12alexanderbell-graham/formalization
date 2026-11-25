import Checked.Math.BERatioCore
import Checked.Math.BEXi5

/-! Bonnor–Ebert sphere, `BEBoundsCore`: route of `Checked.Math.BonnorEbertTurningBounds.bonnor_ebert_turning_bounds` (run 2026-11-25T2228Z). Every sequence of strict extrema of the mass has its sixth term past the start radius (three hundred thousand) of the small ball (`Checked.Math.BEXi5.xi5_gt`). From there on every extremum is a local extremum of u v³, whose logarithmic derivative is g = 2u − v, so g vanishes there (`g_zero_of_ext`); the weighted norm at each of these zeros is at most its value at the start radius, which `Checked.Math.BEAllMain.N0_bounds` bounds, so the segment bounds of `Checked.Math.BERatioCore.Sys.segB_bounds` hold with an error of at most fifty-seven ten-thousandths and u lies within one part in nine hundred ninety of one. `be_num` turns these into the two intervals by bounds on pi, the square root of seven and partial sums of the exponential series. -/

namespace Checked.Math.BEBoundsCore
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

theorem be_exp_lo1 : (9.2 : ℝ) ≤ Real.exp 2.2195 := by
  have := Real.sum_le_exp_of_nonneg (x := (2.2195 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

theorem be_exp_hi1 : Real.exp 2.555 ≤ 12.9 := by
  have := Checked.Math.GSeg.exp_le_pow4 (x := (2.555 : ℝ)) (by norm_num) (by norm_num) 6 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

theorem be_exp_lo2 : (0.2125 : ℝ) ≤ Real.exp (-1.54) := by
  have := Checked.Math.GSeg.exp_le_pow4 (x := (1.54 : ℝ)) (by norm_num) (by norm_num) 6 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  linarith

theorem be_exp_hi2 : Real.exp (-0.882) ≤ 0.4155 := by
  have := Real.sum_le_exp_of_nonneg (x := (0.882 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- The four segment bounds with an error at most `57 / 10000`, and u within `1 / 990` of one at both ends,
give the two quotient intervals. -/
theorem be_num {ε L D a b : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 57 / 10000)
    (h1 : (Real.sqrt 7 / 2 - 16 * ε) * L ≤ Real.pi)
    (h2 : Real.pi ≤ (Real.sqrt 7 / 2 + 16 * ε) * L)
    (h3 : -(1 + 36 * ε) * L ≤ D) (h4 : D ≤ -(1 - 36 * ε) * L)
    (ha : 989 / 990 ≤ a) (ha' : a ≤ 991 / 990) (hb : 989 / 990 ≤ b) (hb' : b ≤ 991 / 990) :
    9.2 ≤ Real.exp L ∧ Real.exp L ≤ 12.9 ∧
      -0.42 ≤ -Real.exp (D / 2) * ((b + 1) / (a + 1)) ∧
      -Real.exp (D / 2) * ((b + 1) / (a + 1)) ≤ -0.21 := by
  obtain ⟨s1, s2⟩ := Checked.Math.GelfandRadiiCore.gr_sqrt7
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have Lpos : 0 < L := by
    by_contra hL
    push Not at hL
    have : (Real.sqrt 7 / 2 + 16 * ε) * L ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hL
    linarith
  have Llo : 2.2195 ≤ L := by
    have : (1.4141 - (Real.sqrt 7 / 2 + 16 * ε)) * L ≥ 0 :=
      mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Lhi : L ≤ 2.555 := by
    have : ((Real.sqrt 7 / 2 - 16 * ε) - 1.2316) * L ≥ 0 :=
      mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Dlo : -1.54 ≤ D / 2 := by
    have : (1.2052 - (1 + 36 * ε)) * L ≥ 0 := mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Dhi : D / 2 ≤ -0.882 := by
    have : ((1 - 36 * ε) - 0.7948) * L ≥ 0 := mul_nonneg (by linarith) Lpos.le
    nlinarith
  have E1 := le_trans be_exp_lo2 (Real.exp_le_exp.2 Dlo)
  have E2 := le_trans (Real.exp_le_exp.2 Dhi) be_exp_hi2
  have ha1 : 0 < a + 1 := by linarith
  have F1 : (1979 / 1981 : ℝ) ≤ (b + 1) / (a + 1) := by
    rw [le_div_iff₀ ha1]; nlinarith
  have F2 : (b + 1) / (a + 1) ≤ 1981 / 1979 := by
    rw [div_le_iff₀ ha1]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans be_exp_lo1 (Real.exp_le_exp.2 Llo)
  · exact le_trans (Real.exp_le_exp.2 Lhi) be_exp_hi1
  · have hF0 : 0 ≤ (b + 1) / (a + 1) := by linarith
    have := mul_le_mul E2 F2 hF0 (by norm_num)
    linarith
  · have hE0 : 0 ≤ Real.exp (D / 2) := (Real.exp_pos _).le
    have := mul_le_mul E1 F1 (by norm_num) hE0
    linarith

/-- At a point beyond `s0` where u v³ changes monotonicity, g = 2u − v vanishes. -/
theorem g_zero_of_ext {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0) {a z b : ℝ} (hz : z ∈ Ici s0)
    (haz : a < z) (hzb : z < b)
    (h : (StrictAntiOn (fun t => U t * V t ^ 3) (Icc a z) ∧
          StrictMonoOn (fun t => U t * V t ^ 3) (Icc z b)) ∨
        (StrictMonoOn (fun t => U t * V t ^ 3) (Icc a z) ∧
          StrictAntiOn (fun t => U t * V t ^ 3) (Icc z b))) :
    2 * U z - V z = 0 := by
  have hd := Checked.Math.BERatioCore.P_deriv S hz
  have h0 : U z * V z ^ 3 * (2 * U z - V z) / z = 0 := by
    rcases h with ⟨hA, hM⟩ | ⟨hM, hA⟩
    · have hloc : IsLocalMin (fun t => U t * V t ^ 3) z := by
        filter_upwards [Icc_mem_nhds haz hzb] with y hy
        rcases le_total y z with hyz | hzy
        · exact hA.antitoneOn ⟨hy.1, hyz⟩ ⟨haz.le, le_rfl⟩ hyz
        · exact hM.monotoneOn ⟨le_rfl, hzb.le⟩ ⟨hzy, hy.2⟩ hzy
      exact hloc.hasDerivAt_eq_zero hd
    · have hloc : IsLocalMax (fun t => U t * V t ^ 3) z := by
        filter_upwards [Icc_mem_nhds haz hzb] with y hy
        rcases le_total y z with hyz | hzy
        · exact hM.monotoneOn ⟨hy.1, hyz⟩ ⟨haz.le, le_rfl⟩ hyz
        · exact hA.antitoneOn ⟨le_rfl, hzb.le⟩ ⟨hzy, hy.2⟩ hzy
      exact hloc.hasDerivAt_eq_zero hd
  have tp := S.tpos hz
  obtain ⟨hu, hv⟩ := S.UV_pos hz
  have hP : 0 < U z * V z ^ 3 := by positivity
  rcases div_eq_zero_iff.1 h0 with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd h'' hP.ne'
    · exact h''
  · exact absurd h' tp.ne'

end Checked.Math.BEBoundsCore
namespace Checked.Math.BEBoundsCore
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (U V Hyp hyp_of U_deriv V_deriv phi_neg U_pos)
open Checked.Math.BERatioCore (P_anti_of_M P_mono_of_M neg_of_antiP pos_of_monoP M_at_zero q_eq32
  neg_one_pow_sq)

theorem bounds_main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) <
          ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) / Real.sqrt (4 * Real.pi)) ∧
      Tendsto (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) atTop
        (𝓝 (Real.sqrt (2 / Real.pi))) ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
        (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi))) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) ∧
      (∀ k : ℕ, 5 ≤ k →
        9.2 ≤ ξ (k + 1) / ξ k ∧ ξ (k + 1) / ξ k ≤ 12.9 ∧
        -0.42 ≤ (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) ∧
        (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) ≤ -0.21) := by
  obtain ⟨ξ, hm, hT, hz0lo, hz0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hR, hQ⟩ :=
    Checked.Math.BERatioCore.main w φ hw hφ0 hφ h0
  refine ⟨ξ, hm, hT, hz0lo, hz0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hR, hQ, ?_⟩
  have x5 := Checked.Math.BEXi5.xi5_gt w φ hw hφ0 hφ h0 ξ hm hz0lo hmax0 hmin hmax
  have E := hyp_of hw hφ0 hφ
  obtain ⟨r1, r2, r3⟩ := Checked.Math.BEAllMain.restrict 300000 hw hφ0 hφ
  obtain ⟨-, su, sv, -⟩ := Checked.Math.BEState300.state300 300000 le_rfl w φ r1 r2 r3 h0
  obtain ⟨N0le, N0pos⟩ := Checked.Math.BEAllMain.N0_bounds su sv
  have N0' : Nw (U w φ 300000 - 1) (V φ 300000 - 2) ≤ 3234 / 100000000 := N0le
  have S : Sys (U w φ) (V φ) 300000 :=
    ⟨by norm_num, fun t ht => U_deriv E (by linarith [mem_Ici.1 ht]),
      fun t ht => V_deriv E (by linarith [mem_Ici.1 ht]), le_trans N0le (by norm_num), N0pos⟩
  have ξpos : ∀ n, 0 < ξ n := fun n =>
    lt_of_lt_of_le (by norm_num at hz0lo; linarith) (hm.monotone (Nat.zero_le n))
  have hKi : ∀ k, 5 ≤ k → ξ k ∈ Ici (300000 : ℝ) := fun k hk =>
    mem_Ici.2 (le_trans x5.le (hm.monotone hk))
  -- the sign of g on each segment from index five on
  have side : ∀ k, 5 ≤ k → ∀ t ∈ Ioo (ξ k) (ξ (k + 1)),
      0 < (-1 : ℝ) ^ (k + 1) * (2 * U w φ t - V φ t) := by
    intro k hk
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · have e : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [e]
      exact neg_of_antiP S (hKi _ hk) (P_anti_of_M E (ξpos _) (hanti m))
    · have e : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]; norm_num
      rw [e]
      exact pos_of_monoP S (hKi _ hk) (P_mono_of_M E (ξpos _) (hmono m))
  -- every extremum from index five on is a zero of g
  have hgz : ∀ n, 5 ≤ n → 2 * U w φ (ξ n) - V φ (ξ n) = 0 := by
    intro n hn
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have e : 2 * (j + 1) = 2 * j + 2 := by ring
      rw [e] at hn ⊢
      have hA := hanti (j + 1)
      rw [e, show 2 * j + 2 + 1 = 2 * j + 3 by ring] at hA
      exact g_zero_of_ext S (hKi _ hn) (hm (by omega : 2 * j + 1 < 2 * j + 2))
        (hm (by omega : 2 * j + 2 < 2 * j + 3))
        (Or.inr ⟨P_mono_of_M E (ξpos _) (hmono j), P_anti_of_M E (ξpos _) hA⟩)
    · exact g_zero_of_ext S (hKi _ hn) (hm (by omega : 2 * m < 2 * m + 1))
        (hm (by omega : 2 * m + 1 < 2 * m + 2))
        (Or.inl ⟨P_anti_of_M E (ξpos _) (hanti m), P_mono_of_M E (ξpos _) (hmono m)⟩)
  intro k hk
  have B := Checked.Math.BERatioCore.Sys.segB_bounds S (neg_one_pow_sq (k + 1)) (hKi k hk)
    (hm (Nat.lt_succ_self k)) (hgz k hk) (hgz (k + 1) (by omega)) (side k hk)
  -- the error and the windows of u at both ends
  have Nk : ∀ n, 5 ≤ n → Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2) ≤ 3234 / 100000000 := fun n hn =>
    le_trans (S.N_le (hKi n hn)) N0'
  have eK : Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) ≤ 57 / 10000 := by
    rw [show (57 / 10000 : ℝ) = Real.sqrt ((57 / 10000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    linarith [Nk k hk]
  have Nz : ∀ n, 5 ≤ n → Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2) = 32 * (U w φ (ξ n) - 1) ^ 2 :=
    fun n hn => (S.at_zero (hKi n hn) (hgz n hn)).1
  have W : ∀ n, 5 ≤ n → 989 / 990 ≤ U w φ (ξ n) ∧ U w φ (ξ n) ≤ 991 / 990 := fun n hn =>
    Checked.Math.BEAllMain.U_win (Nk n hn) (le_of_eq (Nz n hn).symm)
  obtain ⟨wa, wa'⟩ := W k hk
  obtain ⟨wb, wb'⟩ := W (k + 1) (by omega)
  have nb := be_num (Real.sqrt_nonneg _) eK B.1 B.2.1 B.2.2.1 B.2.2.2 wa wa' wb wb'
  -- the radius quotient
  have hratio : ξ (k + 1) / ξ k = Real.exp (Real.log (ξ (k + 1)) - Real.log (ξ k)) := by
    rw [Real.exp_sub, Real.exp_log (ξpos _), Real.exp_log (ξpos _)]
  -- the deviation quotient
  set c := Real.sqrt (2 / Real.pi) with hc
  have c0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have dev : ∀ n, 5 ≤ n →
      ξ n ^ 2 * (-φ (ξ n)) * Real.exp (w (ξ n) / 2) / Real.sqrt (4 * Real.pi) - c =
        c * (U w φ (ξ n) ^ 2 - 1) := fun n hn => M_at_zero E (ξpos n) (hgz n hn)
  have hu0 : 0 < U w φ (ξ k) := U_pos E (ξpos k)
  have hu1 : 0 < U w φ (ξ (k + 1)) := U_pos E (ξpos (k + 1))
  have hs : (U w φ (ξ (k + 1)) - 1) * (U w φ (ξ k) - 1) < 0 := by
    have a : (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) /
        Real.sqrt (4 * Real.pi) - c) *
        (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) - c) < 0 := by
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
      · have a1 := (h2 m).1
        have a2 := (h2 m).2
        exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
      · have a1 := (h2 m).1
        have a2 := (h2 (m + 1)).2
        have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
        rw [e] at a2
        exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
    rw [dev (k + 1) (by omega), dev k hk] at a
    have e : c * (U w φ (ξ (k + 1)) ^ 2 - 1) * (c * (U w φ (ξ k) ^ 2 - 1)) =
        ((U w φ (ξ (k + 1)) - 1) * (U w φ (ξ k) - 1)) *
          (c ^ 2 * (U w φ (ξ (k + 1)) + 1) * (U w φ (ξ k) + 1)) := by ring
    rw [e] at a
    have hpos : 0 < c ^ 2 * (U w φ (ξ (k + 1)) + 1) * (U w φ (ξ k) + 1) := by positivity
    by_contra hc'
    push Not at hc'
    have := mul_nonneg hc' hpos.le
    linarith
  have hx0 : U w φ (ξ k) - 1 ≠ 0 := by rintro h; rw [h] at hs; simp at hs
  have hq := q_eq32 (Nz k hk) (Nz (k + 1) (by omega)) hs
  have hdq : (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
        c) / (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) - c) =
      -Real.exp ((Real.log (Nw (U w φ (ξ (k + 1)) - 1) (V φ (ξ (k + 1)) - 2)) -
          Real.log (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2))) / 2) *
        ((U w φ (ξ (k + 1)) + 1) / (U w φ (ξ k) + 1)) := by
    rw [dev (k + 1) (by omega), dev k hk, ← hq, mul_div_mul_left _ _ c0.ne']
    have h1 : U w φ (ξ k) + 1 ≠ 0 := by positivity
    have h2' : U w φ (ξ k) ^ 2 - 1 ≠ 0 := by
      rw [show U w φ (ξ k) ^ 2 - 1 = (U w φ (ξ k) - 1) * (U w φ (ξ k) + 1) by ring]
      exact mul_ne_zero hx0 h1
    field_simp
    ring
  rw [hratio, hdq]
  exact nb

end Checked.Math.BEBoundsCore
