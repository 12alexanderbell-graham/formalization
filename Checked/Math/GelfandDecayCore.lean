import Checked.Math.GelfandRadiiCore
import Checked.Math.BEDecayCore

/-! Gelfand problem in the three-dimensional ball, `GelfandDecayCore`: route of `Checked.Math.GelfandTurningDecay.gelfand_turning_decay` (run 2026-11-26T1028Z). The proof of `Checked.Math.GelfandRadiiCore.radii_main` gives, at every turning point from index six on, the four segment bounds of `Checked.Math.GelfandRatioCore.Sys.seg_bounds` with an error, the square root of the weighted norm at that turning point, of at most 1386 millionths. At a turning point the weighted norm is eight times the square of u − 1, so the error at the next turning point is the exponential of half the advance of log `Nw` times the error at this one, at most thirty-three hundredths of it, and the error shrinks geometrically by induction (`decay_main`); the advance of log s and half the advance of log `Nw` differ from their limits by a multiple of the error, so both quotients lie within a multiple of the error of their limits (`gdecay_num`, with `Checked.Math.BEDecayCore.exp_diff_le`). -/

namespace Checked.Math.GelfandDecayCore
open Set Filter Topology

set_option maxHeartbeats 4000000 in
/-- The four segment bounds with an error at most `1386 / 1000000` put both quotients within a multiple of
ε of their limits, and the exponential of half the advance of log `Nw` below `33 / 100`. -/
theorem gdecay_num {ε L D : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1386 / 1000000)
    (h1 : (Real.sqrt 7 / 2 - 16 * ε) * L ≤ Real.pi)
    (h2 : Real.pi ≤ (Real.sqrt 7 / 2 + 16 * ε) * L)
    (h3 : -(1 + 36 * ε) * L ≤ D) (h4 : D ≤ -(1 - 36 * ε) * L) :
    |Real.exp L - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤ 336 * ε ∧
      |-Real.exp (D / 2) - -Real.exp (-(Real.pi / Real.sqrt 7))| ≤ 20 * ε ∧
      Real.exp (D / 2) ≤ 33 / 100 := by
  obtain ⟨s1, s2⟩ := Checked.Math.GelfandRadiiCore.gr_sqrt7
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  set s := Real.sqrt 7 with hs
  have spos : 0 < s := by linarith
  have Lpos : 0 < L := by
    by_contra hL
    push Not at hL
    have : (s / 2 + 16 * ε) * L ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hL
    linarith
  have Lhi : L ≤ 2.4154 := by
    have : ((s / 2 - 16 * ε) - 1.300699) * L ≥ 0 :=
      mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Dhi : D / 2 ≤ -1.1094 := by
    have : ((1 - 36 * ε) - 0.950104) * L ≥ 0 := mul_nonneg (by linarith) Lpos.le
    nlinarith
  -- the limit of the advance of log s
  set Ls := 2 * Real.pi / s with hLs
  have hLs' : Ls * s = 2 * Real.pi := by rw [hLs]; field_simp
  have Lshi : Ls ≤ 2.4154 := by
    by_contra h
    push Not at h
    nlinarith
  have Lslo : 2.37 ≤ Ls := by
    by_contra h
    push Not at h
    nlinarith
  have hLd : |L - Ls| ≤ 30 * ε := by
    have u1 : s * (L - Ls) ≤ 32 * ε * L := by nlinarith
    have u2 : -(32 * ε * L) ≤ s * (L - Ls) := by nlinarith
    have w1 : 32 * ε * L ≤ s * (30 * ε) := by nlinarith [mul_le_mul_of_nonneg_left Lhi hε0]
    rw [abs_le]
    constructor
    · by_contra h
      push Not at h
      have : s * (L - Ls) < s * (-(30 * ε)) := mul_lt_mul_of_pos_left h spos
      linarith
    · by_contra h
      push Not at h
      have : s * (30 * ε) < s * (L - Ls) := mul_lt_mul_of_pos_left h spos
      linarith
  have eL : Real.exp L ≤ 11.2 :=
    le_trans (Real.exp_le_exp.2 Lhi) Checked.Math.GelfandRadiiCore.gr_exp_hi1
  have eLs : Real.exp Ls ≤ 11.2 :=
    le_trans (Real.exp_le_exp.2 Lshi) Checked.Math.GelfandRadiiCore.gr_exp_hi1
  have r1 : |Real.exp L - Real.exp Ls| ≤ 336 * ε := by
    have := Checked.Math.BEDecayCore.exp_diff_le eL eLs
    have := mul_le_mul_of_nonneg_left hLd (by norm_num : (0 : ℝ) ≤ 11.2)
    linarith
  -- the limit of half the advance of log Nw
  set Xs := -(Real.pi / s) with hXs
  have hXs' : Xs = -(Ls / 2) := by rw [hXs, hLs]; ring
  have Xshi : Xs ≤ -1.1094 := by rw [hXs']; linarith
  have hXd : |D / 2 - Xs| ≤ 59 * ε := by
    have v1 : D / 2 + L / 2 ≤ 18 * ε * L := by nlinarith
    have v2 : -(18 * ε * L) ≤ D / 2 + L / 2 := by nlinarith
    have v3 : 18 * ε * L ≤ 18 * ε * 2.4154 := by nlinarith [mul_le_mul_of_nonneg_left Lhi hε0]
    have v4 := abs_le.1 hLd
    rw [abs_le, hXs']
    constructor <;> nlinarith
  have eX : Real.exp (D / 2) ≤ 0.33 :=
    le_trans (Real.exp_le_exp.2 Dhi) Checked.Math.GelfandRadiiCore.gr_exp_hi2
  have eXs : Real.exp Xs ≤ 0.33 :=
    le_trans (Real.exp_le_exp.2 Xshi) Checked.Math.GelfandRadiiCore.gr_exp_hi2
  have r2 : |Real.exp (D / 2) - Real.exp Xs| ≤ 20 * ε := by
    have := Checked.Math.BEDecayCore.exp_diff_le eX eXs
    have := mul_le_mul_of_nonneg_left hXd (by norm_num : (0 : ℝ) ≤ 0.33)
    linarith
  refine ⟨r1, ?_, by linarith⟩
  rw [show -Real.exp (D / 2) - -Real.exp Xs = -(Real.exp (D / 2) - Real.exp Xs) by ring, abs_neg]
  exact r2

end Checked.Math.GelfandDecayCore

namespace Checked.Math.GelfandDecayCore
open Set Filter Topology
open Checked.Math.GelfandRatioCore
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (lam U V Hyp hyp_of U_deriv V_deriv lam_deriv lam_eq_UV phi_neg)

set_option maxHeartbeats 4000000 in
/-- The statement of `Checked.Math.GelfandRadiiCore.radii_main` with bounds at index n + 6 that shrink as
(33/100)^n. -/
theorem decay_main (w φ : ℝ → ℝ)
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
        (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) ≤ -0.28) ∧
      (∃ c₁ c₂ q : ℝ, c₁ ≤ 47 / 100 ∧ c₂ ≤ 3 / 100 ∧ 0 ≤ q ∧ q ≤ 33 / 100 ∧
        ∀ n : ℕ,
          |ζ (n + 7) / ζ (n + 6) - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤ c₁ * q ^ n ∧
          |(ζ (n + 7) ^ 2 * Real.exp (w (ζ (n + 7))) - 2) / (ζ (n + 6) ^ 2 * Real.exp (w (ζ (n + 6))) - 2) -
            -Real.exp (-(Real.pi / Real.sqrt 7))| ≤ c₂ * q ^ n) := by
  obtain ⟨ζ, hm, hT, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hQ, hR,
    hB⟩ := Checked.Math.GelfandRadiiCore.radii_main w φ hw hφ0 hφ h0
  refine ⟨ζ, hm, hT, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hQ, hR,
    hB, ?_⟩
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
  have hKi : ∀ k, 6 ≤ k → ζ k ∈ Ici (300000 : ℝ) := fun k hk =>
    mem_Ici.2 (le_trans z6 (hm.monotone hk))
  have side : ∀ k, 6 ≤ k → ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ t ∈ Ioo (ζ k) (ζ (k + 1)), 0 < σ * (V φ t - 2) := by
    intro k hk
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · exact ⟨1, by norm_num, pos_of_anti E S (hKi _ hk) (hanti m)⟩
    · exact ⟨-1, by norm_num, neg_of_mono E S (hKi _ hk) (hmono m)⟩
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
  -- the error at the seventh turning point
  have e6 : Real.sqrt (Nw (U w φ (ζ 6) - 1) (V φ (ζ 6) - 2)) ≤ 1386 / 1000000 := by
    rw [Nz 6]
    have e := lam2 6
    have hx : 0 < U w φ (ζ 6) - 1 := by linarith [l6.1]
    have hx' : U w φ (ζ 6) - 1 ≤ 49 / 100000 := by linarith [l6.2]
    rw [show (1386 / 1000000 : ℝ) = Real.sqrt ((1386 / 1000000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have eK : ∀ k, 6 ≤ k → Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) ≤ 1386 / 1000000 := fun k hk =>
    le_trans (Sys.sqrtN_le S (hKi 6 le_rfl) (hm.monotone hk)) e6
  -- one segment: the error shrinks by 33/100 and both quotients are within a multiple of it
  have seg : ∀ k, 6 ≤ k →
      Real.sqrt (Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2)) ≤
          33 / 100 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) ∧
      |ζ (k + 1) / ζ k - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤
          336 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) ∧
      |(ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) -
        -Real.exp (-(Real.pi / Real.sqrt 7))| ≤
          20 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) := by
    intro k hk
    obtain ⟨σ, hσ, hsg⟩ := side k hk
    have B := Checked.Math.GelfandRatioCore.Sys.seg_bounds S hσ (hKi k hk) (hm (Nat.lt_succ_self k))
      (hVz k) (hVz (k + 1)) hsg
    have nb := gdecay_num (Real.sqrt_nonneg _) (eK k hk) B.1 B.2.1 B.2.2.1 B.2.2.2
    have hratio : ζ (k + 1) / ζ k = Real.exp (Real.log (ζ (k + 1)) - Real.log (ζ k)) := by
      rw [Real.exp_sub, Real.exp_log (ζpos _), Real.exp_log (ζpos _)]
    have hNa := S.N_pos (hKi k hk)
    have hNb := S.N_pos (hKi (k + 1) (by omega))
    set Na := Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2) with hNa'
    set Nb := Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2) with hNb'
    have hnext : Real.sqrt Nb = Real.exp ((Real.log Nb - Real.log Na) / 2) * Real.sqrt Na := by
      have eD : Real.exp ((Real.log Nb - Real.log Na) / 2) ^ 2 = Nb / Na := by
        rw [sq, ← Real.exp_add,
          show (Real.log Nb - Real.log Na) / 2 + (Real.log Nb - Real.log Na) / 2 =
            Real.log Nb - Real.log Na by ring,
          Real.exp_sub, Real.exp_log hNb, Real.exp_log hNa]
      have e1 : Nb = Real.exp ((Real.log Nb - Real.log Na) / 2) ^ 2 * Na := by
        rw [eD]; field_simp
      conv_lhs => rw [e1]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
    have hdq : (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) =
        -Real.exp ((Real.log Nb - Real.log Na) / 2) := by
      rw [lam2 (k + 1), lam2 k]
      have hs : (U w φ (ζ (k + 1)) - 1) * (U w φ (ζ k) - 1) < 0 := by
        have := alt k; rw [lam2 (k + 1), lam2 k] at this; nlinarith
      rw [show 2 * (U w φ (ζ (k + 1)) - 1) / (2 * (U w φ (ζ k) - 1)) =
        (U w φ (ζ (k + 1)) - 1) / (U w φ (ζ k) - 1) by
          rw [mul_div_mul_left _ _ two_ne_zero]]
      exact q_eq (Nz k) (Nz (k + 1)) hs
    refine ⟨?_, ?_, ?_⟩
    · rw [hnext]
      exact mul_le_mul_of_nonneg_right nb.2.2 (Real.sqrt_nonneg _)
    · rw [hratio]; exact nb.1
    · rw [hdq]; exact nb.2.1
  -- the error at index n + 6, by induction
  have eN : ∀ n : ℕ, Real.sqrt (Nw (U w φ (ζ (n + 6)) - 1) (V φ (ζ (n + 6)) - 2)) ≤
      1386 / 1000000 * (33 / 100) ^ n := by
    intro n
    induction n with
    | zero => simpa using eK 6 le_rfl
    | succ n ih =>
      have := (seg (n + 6) (by omega)).1
      rw [show n + 1 + 6 = n + 6 + 1 by omega, pow_succ]
      nlinarith
  refine ⟨47 / 100, 3 / 100, 33 / 100, le_rfl, le_rfl, by norm_num, le_rfl, ?_⟩
  intro n
  have hq0 : (0 : ℝ) ≤ (33 / 100) ^ n := by positivity
  obtain ⟨-, s2, s3⟩ := seg (n + 6) (by omega)
  have e7 : n + 6 + 1 = n + 7 := by omega
  rw [e7] at s2 s3
  have := eN n
  constructor
  · nlinarith
  · nlinarith

end Checked.Math.GelfandDecayCore
