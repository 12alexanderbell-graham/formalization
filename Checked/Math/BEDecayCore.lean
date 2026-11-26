import Checked.Math.BEBoundsCore

/-! Bonnor–Ebert sphere, `BEDecayCore`: route of `Checked.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay` (run 2026-11-26T0428Z). The proof of `Checked.Math.BEBoundsCore.bounds_main` gives, at every extremum from index five on, the four segment bounds of `Checked.Math.BERatioCore.Sys.segB_bounds` with an error, the square root of the weighted norm at that extremum, of at most fifty-seven ten-thousandths. The upper bound on the advance of log `Nw` makes the error at the next extremum at most twenty-one fiftieths of the error at this one, so the error shrinks geometrically by induction (`decay_main`); the advance of log s and half the advance of log `Nw` differ from their limits by a multiple of the error, so both quotients lie within a multiple of the error of their limits (`decay_num`, with `exp_diff_le`). -/

namespace Checked.Math.BEDecayCore
open Set Filter Topology

/-- A Lipschitz bound for the exponential below a common bound of both values. -/
theorem exp_diff_le {x y M : ℝ} (hx : Real.exp x ≤ M) (hy : Real.exp y ≤ M) :
    |Real.exp x - Real.exp y| ≤ M * |x - y| := by
  rcases le_total y x with h | h
  · have e1 := Real.add_one_le_exp (y - x)
    have e2 : Real.exp y = Real.exp x * Real.exp (y - x) := by rw [← Real.exp_add]; ring_nf
    have hex := Real.exp_pos x
    have hle : Real.exp y ≤ Real.exp x := Real.exp_le_exp.2 h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have : Real.exp x - Real.exp y ≤ Real.exp x * (x - y) := by
      rw [e2]; nlinarith
    nlinarith
  · have e1 := Real.add_one_le_exp (x - y)
    have e2 : Real.exp x = Real.exp y * Real.exp (x - y) := by rw [← Real.exp_add]; ring_nf
    have hey := Real.exp_pos y
    have hle : Real.exp x ≤ Real.exp y := Real.exp_le_exp.2 h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have : Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
      rw [e2]; nlinarith
    nlinarith

set_option maxHeartbeats 4000000 in
/-- The four segment bounds with an error at most `57 / 10000`, and u within ε/5 of one at both ends, put
both quotients within a multiple of ε of their limits, and the exponential of half the advance of log `Nw`
below `21 / 50`. -/
theorem decay_num {ε L D a b : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 57 / 10000)
    (h1 : (Real.sqrt 7 / 2 - 16 * ε) * L ≤ Real.pi)
    (h2 : Real.pi ≤ (Real.sqrt 7 / 2 + 16 * ε) * L)
    (h3 : -(1 + 36 * ε) * L ≤ D) (h4 : D ≤ -(1 - 36 * ε) * L)
    (ha : (a - 1) ^ 2 ≤ ε ^ 2 / 25) (hb : (b - 1) ^ 2 ≤ ε ^ 2 / 25) :
    |Real.exp L - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤ 400 * ε ∧
      |-Real.exp (D / 2) * ((b + 1) / (a + 1)) - -Real.exp (-(Real.pi / Real.sqrt 7))| ≤ 26 * ε ∧
      Real.exp (D / 2) ≤ 21 / 50 := by
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
  have Lhi : L ≤ 2.555 := by
    have : ((s / 2 - 16 * ε) - 1.2316) * L ≥ 0 :=
      mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Llo : 2.2195 ≤ L := by
    have : (1.4141 - (s / 2 + 16 * ε)) * L ≥ 0 :=
      mul_nonneg (by linarith) Lpos.le
    nlinarith
  have Dhi : D / 2 ≤ -0.882 := by
    have : ((1 - 36 * ε) - 0.7948) * L ≥ 0 := mul_nonneg (by linarith) Lpos.le
    nlinarith
  -- the limit of the advance of log s
  set Ls := 2 * Real.pi / s with hLs
  have hLs' : Ls * s = 2 * Real.pi := by rw [hLs]; field_simp
  have Lshi : Ls ≤ 2.555 := by
    by_contra h
    push Not at h
    nlinarith
  have hLd : |L - Ls| ≤ 31 * ε := by
    have u1 : s * (L - Ls) ≤ 32 * ε * L := by nlinarith
    have u2 : -(32 * ε * L) ≤ s * (L - Ls) := by nlinarith
    have w1 : 32 * ε * L ≤ s * (31 * ε) := by nlinarith [mul_le_mul_of_nonneg_left Lhi hε0]
    rw [abs_le]
    constructor
    · by_contra h
      push Not at h
      have : s * (L - Ls) < s * (-(31 * ε)) := mul_lt_mul_of_pos_left h spos
      linarith
    · by_contra h
      push Not at h
      have : s * (31 * ε) < s * (L - Ls) := mul_lt_mul_of_pos_left h spos
      linarith
  have eL : Real.exp L ≤ 12.9 :=
    le_trans (Real.exp_le_exp.2 Lhi) Checked.Math.BEBoundsCore.be_exp_hi1
  have eLs : Real.exp Ls ≤ 12.9 :=
    le_trans (Real.exp_le_exp.2 Lshi) Checked.Math.BEBoundsCore.be_exp_hi1
  have r1 : |Real.exp L - Real.exp Ls| ≤ 400 * ε := by
    have := exp_diff_le eL eLs
    have := mul_le_mul_of_nonneg_left hLd (by norm_num : (0 : ℝ) ≤ 12.9)
    linarith
  -- the limit of half the advance of log Nw
  set Xs := -(Real.pi / s) with hXs
  have hXs' : Xs = -(Ls / 2) := by rw [hXs, hLs]; ring
  have Xshi : Xs ≤ -0.882 := by
    have : 2.374 ≤ Ls := by by_contra h; push Not at h; nlinarith
    rw [hXs']; linarith
  have hXd : |D / 2 - Xs| ≤ 62 * ε := by
    have v1 : D / 2 + L / 2 ≤ 18 * ε * L := by nlinarith
    have v2 : -(18 * ε * L) ≤ D / 2 + L / 2 := by nlinarith
    have v3 : 18 * ε * L ≤ 18 * ε * 2.555 := by nlinarith [mul_le_mul_of_nonneg_left Lhi hε0]
    have v4 := abs_le.1 hLd
    rw [abs_le, hXs']
    constructor <;> nlinarith
  have eX : Real.exp (D / 2) ≤ 0.4155 :=
    le_trans (Real.exp_le_exp.2 Dhi) Checked.Math.BEBoundsCore.be_exp_hi2
  have eXs : Real.exp Xs ≤ 0.4155 :=
    le_trans (Real.exp_le_exp.2 Xshi) Checked.Math.BEBoundsCore.be_exp_hi2
  have r2 : |Real.exp (D / 2) - Real.exp Xs| ≤ 0.4155 * (62 * ε) := by
    have := exp_diff_le eX eXs
    have := mul_le_mul_of_nonneg_left hXd (by norm_num : (0 : ℝ) ≤ 0.4155)
    linarith
  -- the factor of u at the two ends
  have hab : ∀ x : ℝ, (x - 1) ^ 2 ≤ ε ^ 2 / 25 → |x - 1| ≤ ε / 5 := fun x hx => by
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [div_pow]; norm_num; linarith
  have aw := abs_le.1 (hab a ha)
  have bw := abs_le.1 (hab b hb)
  have a1 : 0 < a + 1 := by linarith
  have hF : |(b + 1) / (a + 1) - 1| ≤ 0.2003 * ε := by
    have e : (b + 1) / (a + 1) - 1 = (b - a) / (a + 1) := by field_simp; ring
    rw [e, abs_div, abs_of_pos a1, div_le_iff₀ a1, abs_le]
    constructor <;> nlinarith
  have r3 : |-Real.exp (D / 2) * ((b + 1) / (a + 1)) - -Real.exp Xs| ≤ 26 * ε := by
    have e : -Real.exp (D / 2) * ((b + 1) / (a + 1)) - -Real.exp Xs =
        -(Real.exp (D / 2) * ((b + 1) / (a + 1) - 1)) - (Real.exp (D / 2) - Real.exp Xs) := by ring
    rw [e]
    have t1 : |Real.exp (D / 2) * ((b + 1) / (a + 1) - 1)| ≤ 0.4155 * (0.2003 * ε) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul eX hF (abs_nonneg _) (by norm_num)
    have := abs_sub (-(Real.exp (D / 2) * ((b + 1) / (a + 1) - 1))) (Real.exp (D / 2) - Real.exp Xs)
    rw [abs_neg] at this
    linarith
  exact ⟨r1, r3, by linarith⟩

end Checked.Math.BEDecayCore

namespace Checked.Math.BEDecayCore
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (U V Hyp hyp_of U_deriv V_deriv phi_neg U_pos)
open Checked.Math.BERatioCore (P_anti_of_M P_mono_of_M neg_of_antiP pos_of_monoP M_at_zero q_eq32
  neg_one_pow_sq)

set_option maxHeartbeats 4000000 in
/-- The statement of `Checked.Math.BEBoundsCore.bounds_main` with bounds at index n + 5 that shrink as
(21/50)^n. -/
theorem decay_main (w φ : ℝ → ℝ)
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
            Real.sqrt (2 / Real.pi)) ≤ -0.21) ∧
      (∃ c₁ c₂ q : ℝ, c₁ ≤ 23 / 10 ∧ c₂ ≤ 3 / 20 ∧ 0 ≤ q ∧ q ≤ 21 / 50 ∧
        ∀ n : ℕ,
          |ξ (n + 6) / ξ (n + 5) - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤ c₁ * q ^ n ∧
          |(ξ (n + 6) ^ 2 * (-φ (ξ (n + 6))) * Real.exp (w (ξ (n + 6)) / 2) / Real.sqrt (4 * Real.pi) -
                Real.sqrt (2 / Real.pi)) /
              (ξ (n + 5) ^ 2 * (-φ (ξ (n + 5))) * Real.exp (w (ξ (n + 5)) / 2) / Real.sqrt (4 * Real.pi) -
                Real.sqrt (2 / Real.pi)) -
            -Real.exp (-(Real.pi / Real.sqrt 7))| ≤ c₂ * q ^ n) := by
  obtain ⟨ξ, hm, hT, hz0lo, hz0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hR, hQ, hB⟩ :=
    Checked.Math.BEBoundsCore.bounds_main w φ hw hφ0 hφ h0
  refine ⟨ξ, hm, hT, hz0lo, hz0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hR, hQ, hB, ?_⟩
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
      exact Checked.Math.BEBoundsCore.g_zero_of_ext S (hKi _ hn) (hm (by omega : 2 * j + 1 < 2 * j + 2))
        (hm (by omega : 2 * j + 2 < 2 * j + 3))
        (Or.inr ⟨P_mono_of_M E (ξpos _) (hmono j), P_anti_of_M E (ξpos _) hA⟩)
    · exact Checked.Math.BEBoundsCore.g_zero_of_ext S (hKi _ hn) (hm (by omega : 2 * m < 2 * m + 1))
        (hm (by omega : 2 * m + 1 < 2 * m + 2))
        (Or.inl ⟨P_anti_of_M E (ξpos _) (hanti m), P_mono_of_M E (ξpos _) (hmono m)⟩)
  have Nk : ∀ n, 5 ≤ n → Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2) ≤ 3234 / 100000000 := fun n hn =>
    le_trans (S.N_le (hKi n hn)) N0'
  have eK : ∀ n, 5 ≤ n → Real.sqrt (Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2)) ≤ 57 / 10000 := by
    intro n hn
    rw [show (57 / 10000 : ℝ) = Real.sqrt ((57 / 10000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    linarith [Nk n hn]
  have Nz : ∀ n, 5 ≤ n → Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2) = 32 * (U w φ (ξ n) - 1) ^ 2 :=
    fun n hn => (S.at_zero (hKi n hn) (hgz n hn)).1
  -- u within ε / 5 of one, for any ε at least the square root of the weighted norm there
  have uW : ∀ n, 5 ≤ n → ∀ e : ℝ, Real.sqrt (Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2)) ≤ e →
      (U w φ (ξ n) - 1) ^ 2 ≤ e ^ 2 / 25 := by
    intro n hn e he
    have hN := S.N_pos (hKi n hn)
    have hsq := Real.sq_sqrt hN.le
    have h0' := Real.sqrt_nonneg (Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2))
    have : Real.sqrt (Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2)) ^ 2 ≤ e ^ 2 :=
      pow_le_pow_left₀ h0' he 2
    rw [Nz n hn] at hsq this
    nlinarith [sq_nonneg (U w φ (ξ n) - 1)]
  set c := Real.sqrt (2 / Real.pi) with hc
  have c0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have dev : ∀ n, 5 ≤ n →
      ξ n ^ 2 * (-φ (ξ n)) * Real.exp (w (ξ n) / 2) / Real.sqrt (4 * Real.pi) - c =
        c * (U w φ (ξ n) ^ 2 - 1) := fun n hn => M_at_zero E (ξpos n) (hgz n hn)
  -- one segment: the error shrinks by 21/50 and both quotients are within a multiple of it
  have seg : ∀ k, 5 ≤ k →
      Real.sqrt (Nw (U w φ (ξ (k + 1)) - 1) (V φ (ξ (k + 1)) - 2)) ≤
          21 / 50 * Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) ∧
      |ξ (k + 1) / ξ k - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤
          400 * Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) ∧
      |(ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) - c) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) - c) -
        -Real.exp (-(Real.pi / Real.sqrt 7))| ≤
          26 * Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) := by
    intro k hk
    have B := Checked.Math.BERatioCore.Sys.segB_bounds S (neg_one_pow_sq (k + 1)) (hKi k hk)
      (hm (Nat.lt_succ_self k)) (hgz k hk) (hgz (k + 1) (by omega)) (side k hk)
    have hb' : Real.sqrt (Nw (U w φ (ξ (k + 1)) - 1) (V φ (ξ (k + 1)) - 2)) ≤
        Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) :=
      Checked.Math.GelfandRatioCore.Sys.sqrtN_le S (hKi k hk) (hm (Nat.lt_succ_self k)).le
    have nb := Checked.Math.BEDecayCore.decay_num (Real.sqrt_nonneg _) (eK k hk) B.1 B.2.1 B.2.2.1 B.2.2.2
      (uW k hk _ le_rfl) (uW (k + 1) (by omega) _ hb')
    -- the radius quotient
    have hratio : ξ (k + 1) / ξ k = Real.exp (Real.log (ξ (k + 1)) - Real.log (ξ k)) := by
      rw [Real.exp_sub, Real.exp_log (ξpos _), Real.exp_log (ξpos _)]
    -- the next error
    have hNa := S.N_pos (hKi k hk)
    have hNb := S.N_pos (hKi (k + 1) (by omega))
    set Na := Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2) with hNa'
    set Nb := Nw (U w φ (ξ (k + 1)) - 1) (V φ (ξ (k + 1)) - 2) with hNb'
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
    -- the deviation quotient
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
        -Real.exp ((Real.log Nb - Real.log Na) / 2) *
          ((U w φ (ξ (k + 1)) + 1) / (U w φ (ξ k) + 1)) := by
      rw [dev (k + 1) (by omega), dev k hk, ← hq, mul_div_mul_left _ _ c0.ne']
      have h1 : U w φ (ξ k) + 1 ≠ 0 := by positivity
      have h2' : U w φ (ξ k) ^ 2 - 1 ≠ 0 := by
        rw [show U w φ (ξ k) ^ 2 - 1 = (U w φ (ξ k) - 1) * (U w φ (ξ k) + 1) by ring]
        exact mul_ne_zero hx0 h1
      field_simp
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hnext]
      exact mul_le_mul_of_nonneg_right nb.2.2 (Real.sqrt_nonneg _)
    · rw [hratio]; exact nb.1
    · rw [hdq]; exact nb.2.1
  -- the error at index n + 5, by induction
  have eN : ∀ n : ℕ, Real.sqrt (Nw (U w φ (ξ (n + 5)) - 1) (V φ (ξ (n + 5)) - 2)) ≤
      57 / 10000 * (21 / 50) ^ n := by
    intro n
    induction n with
    | zero => simpa using eK 5 le_rfl
    | succ n ih =>
      have := (seg (n + 5) (by omega)).1
      rw [show n + 1 + 5 = n + 5 + 1 by omega, pow_succ]
      nlinarith
  refine ⟨23 / 10, 3 / 20, 21 / 50, le_rfl, le_rfl, by norm_num, le_rfl, ?_⟩
  intro n
  have hq0 : (0 : ℝ) ≤ (21 / 50) ^ n := by positivity
  obtain ⟨-, s2, s3⟩ := seg (n + 5) (by omega)
  have e6 : n + 5 + 1 = n + 6 := by omega
  rw [e6] at s2 s3
  have := eN n
  constructor
  · nlinarith
  · nlinarith

end Checked.Math.BEDecayCore
