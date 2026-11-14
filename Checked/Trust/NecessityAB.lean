import Checked.FSNeg.LFlowCells
import Checked.FSNeg.LTube
import Checked.FSNeg.LOver
import Checked.FSNeg.LSlow
import Checked.FalknerSkan.NegReversed
import Checked.FalknerSkan.NegWindow
import Checked.Trust.NonVacuity

/-! Hypothesis necessity for the window and the strict upper bound of the attached Falkner–Skan wall shear at the
adverse pressure-gradient coefficient of minus one tenth (`Checked.FalknerSkan.NegWindow`): the wall conditions
are needed. Witness: the reversed-flow solution of the same equation (the construction behind the Checked
headline `fs_neg_tenth_reversed`, `LFlowCells.core_lower_flow`), translated along the half-line, as in
`Checked.Trust.NecessityY` for the rows of Ganapol's table. Translated to the point where its velocity returns to
zero it has p(0) = 0, blowing at the wall and a wall shear below the window; translated to the point where its
stream function returns to zero it has f(0) = 0, a wall moving downstream and a wall shear above the window and
above the strict upper bound. The points and the shear there are located by the certified cells of its tube
(`Checked.FSNeg.LTube`), the second inside one cell by the Taylor-shifted cell polynomial. Run 2026-11-14T0228Z. -/

namespace Checked.Trust.NCAB

open Set Filter Topology Checked.Sim Checked.Sim.QPoly Checked.FSNeg.NCellWC Checked.FSNeg.NBase
  Checked.FSNeg.NFlow Checked.FSNeg.LCell Checked.FSNeg.LFlowCells

theorem ball_c0 {Y : ℝ → ℝ × ℝ × ℝ} {α : ℝ} (h0 : Y 0 = (0, 0, α))
    (hα : |α - -4444461495 / 10000000000| ≤ 1 / 5000000000) :
    InBox Checked.FSNeg.LTube.c0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
  have z0 : ((Checked.FSNeg.LTube.c0.t0 : ℚ) : ℝ) = 0 := by simp [Checked.FSNeg.LTube.c0]
  unfold InBox; simp only [z0, h0]
  simp only [V, Checked.FSNeg.LTube.c0, List.headD_cons]; push_cast
  have hα' := abs_le.1 hα
  nlinarith [hα'.1, hα'.2]

/-- Every solution of the clamped field from (0, 0, α), α in the tube's ball, has a zero of p in
[7/8, 29/32] (cell 28 of the tube) at which 43/100 ≤ q ≤ 13/25. -/
theorem cross_p {Y : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc (0 : ℝ) (3 / 2 : ℝ), HasDerivWithinAt Y (vN t (Y t)) (Icc 0 (3 / 2 : ℝ)) t)
    {α : ℝ} (h0 : Y 0 = (0, 0, α)) (hα : |α - -4444461495 / 10000000000| ≤ 1 / 5000000000) :
    ∃ t ∈ Icc (7 / 8 : ℝ) (29 / 32 : ℝ), (Y t).2.1 = 0 ∧
      (43 / 100 : ℝ) ≤ (Y t).2.2 ∧ (Y t).2.2 ≤ (13 / 25 : ℝ) := by
  have hX : (((3/2 : ℚ) : ℚ) : ℝ) = (3 / 2 : ℝ) := by norm_num
  have hs : SolC (((3/2 : ℚ) : ℚ) : ℝ) 0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    rw [hX]
    exact ⟨fun t ht => (hY t ht).fst, fun t ht => (hY t ht).snd.fst, fun t ht => (hY t ht).snd.snd⟩
  have b0 := ball_c0 h0 hα
  obtain ⟨b1, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) Checked.FSNeg.LTube.c10 [Checked.FSNeg.LTube.c1, Checked.FSNeg.LTube.c2, Checked.FSNeg.LTube.c3, Checked.FSNeg.LTube.c4, Checked.FSNeg.LTube.c5, Checked.FSNeg.LTube.c6, Checked.FSNeg.LTube.c7, Checked.FSNeg.LTube.c8, Checked.FSNeg.LTube.c9] Checked.FSNeg.LTube.c0 Checked.FSNeg.LTube.seg0_ok hs b0
  obtain ⟨b2, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) Checked.FSNeg.LTube.c20 [Checked.FSNeg.LTube.c11, Checked.FSNeg.LTube.c12, Checked.FSNeg.LTube.c13, Checked.FSNeg.LTube.c14, Checked.FSNeg.LTube.c15, Checked.FSNeg.LTube.c16, Checked.FSNeg.LTube.c17, Checked.FSNeg.LTube.c18, Checked.FSNeg.LTube.c19] Checked.FSNeg.LTube.c10 Checked.FSNeg.LTube.seg1_ok hs b1
  obtain ⟨k28, x28⟩ := chain_box [Checked.FSNeg.LTube.c21, Checked.FSNeg.LTube.c22, Checked.FSNeg.LTube.c23, Checked.FSNeg.LTube.c24, Checked.FSNeg.LTube.c25, Checked.FSNeg.LTube.c26, Checked.FSNeg.LTube.c27, Checked.FSNeg.LTube.c28, Checked.FSNeg.LTube.c29] Checked.FSNeg.LTube.c20 Checked.FSNeg.LTube.seg2_ok hs b2 Checked.FSNeg.LTube.c28 (by simp)
  obtain ⟨k29, x29⟩ := chain_box [Checked.FSNeg.LTube.c21, Checked.FSNeg.LTube.c22, Checked.FSNeg.LTube.c23, Checked.FSNeg.LTube.c24, Checked.FSNeg.LTube.c25, Checked.FSNeg.LTube.c26, Checked.FSNeg.LTube.c27, Checked.FSNeg.LTube.c28, Checked.FSNeg.LTube.c29] Checked.FSNeg.LTube.c20 Checked.FSNeg.LTube.seg2_ok hs b2 Checked.FSNeg.LTube.c29 (by simp)
  have e28a : ((Checked.FSNeg.LTube.c28.t0 : ℚ) : ℝ) = (7 / 8 : ℝ) := by norm_num [Checked.FSNeg.LTube.c28]
  have e28b : ((Checked.FSNeg.LTube.c28.t0 : ℚ) : ℝ) + ((Checked.FSNeg.LTube.c28.h : ℚ) : ℝ) = (29 / 32 : ℝ) := by norm_num [Checked.FSNeg.LTube.c28]
  have e29a : ((Checked.FSNeg.LTube.c29.t0 : ℚ) : ℝ) = (29 / 32 : ℝ) := by norm_num [Checked.FSNeg.LTube.c29]
  have B28 := fun t (ht : t ∈ Icc (7 / 8 : ℝ) (29 / 32 : ℝ)) => cell_bounds Checked.FSNeg.LTube.c28 k28 hs x28 t (by rw [e28b, e28a]; exact ht)
  have nqa := (Rat.cast_le (K := ℝ)).2 (show (43/100 : ℚ) ≤ qlo Checked.FSNeg.LTube.c28 - Checked.FSNeg.LTube.c28.B by decide +kernel)
  have nqb := (Rat.cast_le (K := ℝ)).2 (show qhi Checked.FSNeg.LTube.c28 + Checked.FSNeg.LTube.c28.B ≤ (13/25 : ℚ) by decide +kernel)
  have nqc : (((43/100 : ℚ) : ℚ) : ℝ) = (43 / 100 : ℝ) := by norm_num
  have nqd : (((13/25 : ℚ) : ℚ) : ℝ) = (13 / 25 : ℝ) := by norm_num
  have ni := (Rat.cast_lt (K := ℝ)).2 (show Checked.FSNeg.LTube.c28.pp.headD 0 + Checked.FSNeg.LTube.c28.r2 < 0 by decide +kernel)
  have nj := (Rat.cast_lt (K := ℝ)).2 (show 0 < Checked.FSNeg.LTube.c29.pp.headD 0 - Checked.FSNeg.LTube.c29.r2 by decide +kernel)
  rw [Rat.cast_zero] at ni nj
  have hpa : (Y (7 / 8 : ℝ)).2.1 < 0 := by
    have := cell_start Checked.FSNeg.LTube.c28 k28 hs x28
    rw [e28a] at this
    linarith [this.2.2.2]
  have hpb : 0 < (Y (29 / 32 : ℝ)).2.1 := by
    have := cell_start Checked.FSNeg.LTube.c29 k29 hs x29
    rw [e29a] at this
    linarith [this.2.2.1]
  have hcont : ContinuousOn (fun t => (Y t).2.1) (Icc (7 / 8 : ℝ) (29 / 32 : ℝ)) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (3 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hY t ht').continuousWithinAt.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).snd.fst
  obtain ⟨t, ht, hz⟩ := Checked.FSRev.RFlowCells.cross (by norm_num) hcont hpa hpb
  refine ⟨t, ht, hz, ?_⟩
  have c := B28 t ht
  exact ⟨by linarith [c.2.2.2.2.1], by linarith [c.2.2.2.2.2]⟩

open Checked.FSRev.RFlowCells in
/-- Every solution of the clamped field from (0, 0, α), α in the tube's ball, has a zero of the stream
function in [2677/2048, 2679/2048] (inside cell 41 of the tube) at which 1013/1000 ≤ q ≤ 127/125. -/
theorem cross_g {Y : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc (0 : ℝ) (3 / 2 : ℝ), HasDerivWithinAt Y (vN t (Y t)) (Icc 0 (3 / 2 : ℝ)) t)
    {α : ℝ} (h0 : Y 0 = (0, 0, α)) (hα : |α - -4444461495 / 10000000000| ≤ 1 / 5000000000) :
    ∃ t ∈ Icc (2677 / 2048 : ℝ) (2679 / 2048 : ℝ), (Y t).1 = 0 ∧
      (1013 / 1000 : ℝ) ≤ (Y t).2.2 ∧ (Y t).2.2 ≤ (127 / 125 : ℝ) := by
  have hX : (((3/2 : ℚ) : ℚ) : ℝ) = (3 / 2 : ℝ) := by norm_num
  have hs : SolC (((3/2 : ℚ) : ℚ) : ℝ) 0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    rw [hX]
    exact ⟨fun t ht => (hY t ht).fst, fun t ht => (hY t ht).snd.fst, fun t ht => (hY t ht).snd.snd⟩
  have b0 := ball_c0 h0 hα
  obtain ⟨b1, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) Checked.FSNeg.LTube.c10 [Checked.FSNeg.LTube.c1, Checked.FSNeg.LTube.c2, Checked.FSNeg.LTube.c3, Checked.FSNeg.LTube.c4, Checked.FSNeg.LTube.c5, Checked.FSNeg.LTube.c6, Checked.FSNeg.LTube.c7, Checked.FSNeg.LTube.c8, Checked.FSNeg.LTube.c9] Checked.FSNeg.LTube.c0 Checked.FSNeg.LTube.seg0_ok hs b0
  obtain ⟨b2, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) Checked.FSNeg.LTube.c20 [Checked.FSNeg.LTube.c11, Checked.FSNeg.LTube.c12, Checked.FSNeg.LTube.c13, Checked.FSNeg.LTube.c14, Checked.FSNeg.LTube.c15, Checked.FSNeg.LTube.c16, Checked.FSNeg.LTube.c17, Checked.FSNeg.LTube.c18, Checked.FSNeg.LTube.c19] Checked.FSNeg.LTube.c10 Checked.FSNeg.LTube.seg1_ok hs b1
  obtain ⟨b3, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) Checked.FSNeg.LTube.c30 [Checked.FSNeg.LTube.c21, Checked.FSNeg.LTube.c22, Checked.FSNeg.LTube.c23, Checked.FSNeg.LTube.c24, Checked.FSNeg.LTube.c25, Checked.FSNeg.LTube.c26, Checked.FSNeg.LTube.c27, Checked.FSNeg.LTube.c28, Checked.FSNeg.LTube.c29] Checked.FSNeg.LTube.c20 Checked.FSNeg.LTube.seg2_ok hs b2
  obtain ⟨b4, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) Checked.FSNeg.LTube.c40 [Checked.FSNeg.LTube.c31, Checked.FSNeg.LTube.c32, Checked.FSNeg.LTube.c33, Checked.FSNeg.LTube.c34, Checked.FSNeg.LTube.c35, Checked.FSNeg.LTube.c36, Checked.FSNeg.LTube.c37, Checked.FSNeg.LTube.c38, Checked.FSNeg.LTube.c39] Checked.FSNeg.LTube.c30 Checked.FSNeg.LTube.seg3_ok hs b3
  obtain ⟨kc, xc⟩ := chain_box [Checked.FSNeg.LTube.c41, Checked.FSNeg.LTube.c42, Checked.FSNeg.LTube.c43, Checked.FSNeg.LTube.c44, Checked.FSNeg.LTube.c45, Checked.FSNeg.LTube.c46, Checked.FSNeg.LTube.c47] Checked.FSNeg.LTube.c40 Checked.FSNeg.LTube.seg4_ok hs b4 Checked.FSNeg.LTube.c41 (by simp)
  have E1 : ((Checked.FSNeg.LTube.c41.t0 : ℚ) : ℝ) + (((53/2048 : ℚ) : ℚ) : ℝ) = (2677 / 2048 : ℝ) := by norm_num [Checked.FSNeg.LTube.c41]
  have E2 : ((Checked.FSNeg.LTube.c41.t0 : ℚ) : ℝ) + (((55/2048 : ℚ) : ℚ) : ℝ) = (2679 / 2048 : ℝ) := by norm_num [Checked.FSNeg.LTube.c41]
  have hb1 : ((53/2048 : ℚ) : ℚ) ≤ Checked.FSNeg.LTube.c41.h := by decide +kernel
  have hb2 : ((55/2048 : ℚ) : ℚ) ≤ Checked.FSNeg.LTube.c41.h := by decide +kernel
  have SA := sub_bounds Checked.FSNeg.LTube.c41 kc hs xc (53/2048 : ℚ) (53/2048 : ℚ) (by norm_num) le_rfl hb1 (2677 / 2048 : ℝ) (by rw [E1]; exact ⟨le_rfl, le_rfl⟩)
  have SB := sub_bounds Checked.FSNeg.LTube.c41 kc hs xc (55/2048 : ℚ) (55/2048 : ℚ) (by norm_num) le_rfl hb2 (2679 / 2048 : ℝ) (by rw [E2]; exact ⟨le_rfl, le_rfl⟩)
  have SQ := fun t (ht : t ∈ Icc (2677 / 2048 : ℝ) (2679 / 2048 : ℝ)) => sub_bounds Checked.FSNeg.LTube.c41 kc hs xc (53/2048 : ℚ) (55/2048 : ℚ) (by norm_num) (by norm_num) hb2 t (by rw [E1, E2]; exact ht)
  have ni := (Rat.cast_lt (K := ℝ)).2 (show shi Checked.FSNeg.LTube.c41.pg (53/2048 : ℚ) ((53/2048 : ℚ) - (53/2048 : ℚ)) + Checked.FSNeg.LTube.c41.r1 < 0 by decide +kernel)
  have nj := (Rat.cast_lt (K := ℝ)).2 (show 0 < slo Checked.FSNeg.LTube.c41.pg (55/2048 : ℚ) ((55/2048 : ℚ) - (55/2048 : ℚ)) - Checked.FSNeg.LTube.c41.r1 by decide +kernel)
  rw [Rat.cast_zero] at ni nj
  have nqa := (Rat.cast_le (K := ℝ)).2 (show (1013/1000 : ℚ) ≤ slo Checked.FSNeg.LTube.c41.pq (53/2048 : ℚ) ((55/2048 : ℚ) - (53/2048 : ℚ)) - Checked.FSNeg.LTube.c41.B by decide +kernel)
  have nqb := (Rat.cast_le (K := ℝ)).2 (show shi Checked.FSNeg.LTube.c41.pq (53/2048 : ℚ) ((55/2048 : ℚ) - (53/2048 : ℚ)) + Checked.FSNeg.LTube.c41.B ≤ (127/125 : ℚ) by decide +kernel)
  have nqc : (((1013/1000 : ℚ) : ℚ) : ℝ) = (1013 / 1000 : ℝ) := by norm_num
  have nqd : (((127/125 : ℚ) : ℚ) : ℝ) = (127 / 125 : ℝ) := by norm_num
  have hpa : (Y (2677 / 2048 : ℝ)).1 < 0 := by
    linarith [SA.2.1]
  have hpb : 0 < (Y (2679 / 2048 : ℝ)).1 := by
    linarith [SB.1]
  have hcont : ContinuousOn (fun t => (Y t).1) (Icc (2677 / 2048 : ℝ) (2679 / 2048 : ℝ)) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (3 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hY t ht').continuousWithinAt.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).fst
  obtain ⟨t, ht, hz⟩ := cross (by norm_num) hcont hpa hpb
  refine ⟨t, ht, hz, ?_⟩
  have c := SQ t ht
  exact ⟨by linarith [c.2.2.2.2.1], by linarith [c.2.2.2.2.2]⟩
/-- In `fs_neg_tenth_window`, the wall condition f(0) = 0 is needed: the reversed-flow solution translated to the point where its velocity returns to zero (blowing at the wall) meets every other hypothesis and has a wall shear below the window. -/
theorem fs_neg_tenth_window_h4 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 4 := by
  obtain ⟨a, hla, hah, A, B, C, hlim, hpb, hdec⟩ := core_lower_flow (by norm_num)
    ⟨15 / 4, by norm_num, fun _ hY h0 => Checked.FSNeg.LOver.chainC hY h0⟩
    ⟨4, by norm_num, fun _ hY h0 => Checked.FSNeg.LSlow.chainC hY h0⟩ Checked.FalknerSkan.NegReversed.tube
  have hα : |a - -4444461495 / 10000000000| ≤ 1 / 5000000000 := by
    rw [abs_le]; constructor <;> linarith
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 < (flow a (η / Real.sqrt 10)).2.1 ∧ (flow a (η / Real.sqrt 10)).2.1 < 1 :=
    fun η hη => ⟨by linarith [(hpb η hη).1], (hpb η hη).2⟩
  obtain ⟨t, ht, hz, hqL, hqU⟩ := cross_p (flow_sol a (3 / 2)) (flow_zero _) hα
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have hs : 0 ≤ Real.sqrt 10 * t := mul_nonneg hc.le ht0
  have hst : Real.sqrt 10 * t / Real.sqrt 10 = t := by field_simp
  have hq0 : 0 < (flow a (Real.sqrt 10 * t / Real.sqrt 10)).2.2 / Real.sqrt 10 := by
    rw [hst]; exact div_pos (by linarith) hc
  have hpos := Checked.FSRev.RFlowCells.pos_after (β := -1 / 10) (by norm_num) C hb hs hq0
  have A' := Checked.FSRev.RFlowCells.shift_deriv hs A
  have B' := Checked.FSRev.RFlowCells.shift_deriv hs B
  have C' := Checked.FSRev.RFlowCells.shift_deriv hs C
  refine ⟨fun x => Real.sqrt 10 * (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).1,
    fun x => (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).2.1,
    fun x => (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).2.2 / Real.sqrt 10,
    A', B', C', ?_, Checked.FSRev.RFlowCells.shift_lim _ hlim, ?_, Checked.FSRev.RFlowCells.shift_dec _ hdec, ?_⟩
  · show (flow a ((0 + Real.sqrt 10 * t) / Real.sqrt 10)).2.1 = 0
    rw [zero_add, hst]; exact hz
  · intro η hη
    exact hpos (η + Real.sqrt 10 * t) (by linarith [mem_Ici.1 hη])
  · have e : (flow a ((0 + Real.sqrt 10 * t) / Real.sqrt 10)).2.2 / Real.sqrt 10 = (flow a t).2.2 / Real.sqrt 10 := by
      rw [zero_add, hst]
    rintro ⟨h1, -⟩
    beta_reduce at h1
    rw [e] at h1
    have hr : (3162 / 1000 : ℝ) < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    rw [lt_div_iff₀ hc] at h1
    nlinarith
/-- In `fs_neg_tenth_window`, the wall condition p(0) = 0 is needed: the reversed-flow solution translated to the point where its stream function returns to zero (a wall moving downstream) meets every other hypothesis and has a wall shear above the window. -/
theorem fs_neg_tenth_window_h5 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 5 := by
  obtain ⟨a, hla, hah, A, B, C, hlim, hpb, hdec⟩ := core_lower_flow (by norm_num)
    ⟨15 / 4, by norm_num, fun _ hY h0 => Checked.FSNeg.LOver.chainC hY h0⟩
    ⟨4, by norm_num, fun _ hY h0 => Checked.FSNeg.LSlow.chainC hY h0⟩ Checked.FalknerSkan.NegReversed.tube
  have hα : |a - -4444461495 / 10000000000| ≤ 1 / 5000000000 := by
    rw [abs_le]; constructor <;> linarith
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 < (flow a (η / Real.sqrt 10)).2.1 ∧ (flow a (η / Real.sqrt 10)).2.1 < 1 :=
    fun η hη => ⟨by linarith [(hpb η hη).1], (hpb η hη).2⟩
  obtain ⟨t, ht, hz, hqL, hqU⟩ := cross_g (flow_sol a (3 / 2)) (flow_zero _) hα
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have hs : 0 ≤ Real.sqrt 10 * t := mul_nonneg hc.le ht0
  have hst : Real.sqrt 10 * t / Real.sqrt 10 = t := by field_simp
  have hq0 : 0 < (flow a (Real.sqrt 10 * t / Real.sqrt 10)).2.2 / Real.sqrt 10 := by
    rw [hst]; exact div_pos (by linarith) hc
  have hpos := Checked.FSRev.RFlowCells.pos_after (β := -1 / 10) (by norm_num) C hb hs hq0
  have A' := Checked.FSRev.RFlowCells.shift_deriv hs A
  have B' := Checked.FSRev.RFlowCells.shift_deriv hs B
  have C' := Checked.FSRev.RFlowCells.shift_deriv hs C
  refine ⟨fun x => Real.sqrt 10 * (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).1,
    fun x => (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).2.1,
    fun x => (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).2.2 / Real.sqrt 10,
    A', B', C', ?_, Checked.FSRev.RFlowCells.shift_lim _ hlim, ?_, Checked.FSRev.RFlowCells.shift_dec _ hdec, ?_⟩
  · show Real.sqrt 10 * (flow a ((0 + Real.sqrt 10 * t) / Real.sqrt 10)).1 = 0
    rw [zero_add, hst, hz, mul_zero]
  · intro η hη
    exact hpos (η + Real.sqrt 10 * t) (by linarith [mem_Ici.1 hη])
  · have e : (flow a ((0 + Real.sqrt 10 * t) / Real.sqrt 10)).2.2 / Real.sqrt 10 = (flow a t).2.2 / Real.sqrt 10 := by
      rw [zero_add, hst]
    rintro ⟨-, h2⟩
    beta_reduce at h2
    rw [e] at h2
    have hr : Real.sqrt 10 < (31623 / 10000 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    rw [div_lt_iff₀ hc] at h2
    nlinarith
/-- In `fs_neg_tenth_monotone_lt`, the wall condition p(0) = 0 is needed: the same translate has a wall shear above the bound. -/
theorem fs_neg_tenth_monotone_lt_h5 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt 5 := by
  obtain ⟨a, hla, hah, A, B, C, hlim, hpb, hdec⟩ := core_lower_flow (by norm_num)
    ⟨15 / 4, by norm_num, fun _ hY h0 => Checked.FSNeg.LOver.chainC hY h0⟩
    ⟨4, by norm_num, fun _ hY h0 => Checked.FSNeg.LSlow.chainC hY h0⟩ Checked.FalknerSkan.NegReversed.tube
  have hα : |a - -4444461495 / 10000000000| ≤ 1 / 5000000000 := by
    rw [abs_le]; constructor <;> linarith
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 < (flow a (η / Real.sqrt 10)).2.1 ∧ (flow a (η / Real.sqrt 10)).2.1 < 1 :=
    fun η hη => ⟨by linarith [(hpb η hη).1], (hpb η hη).2⟩
  obtain ⟨t, ht, hz, hqL, hqU⟩ := cross_g (flow_sol a (3 / 2)) (flow_zero _) hα
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have hs : 0 ≤ Real.sqrt 10 * t := mul_nonneg hc.le ht0
  have hst : Real.sqrt 10 * t / Real.sqrt 10 = t := by field_simp
  have hq0 : 0 < (flow a (Real.sqrt 10 * t / Real.sqrt 10)).2.2 / Real.sqrt 10 := by
    rw [hst]; exact div_pos (by linarith) hc
  have hpos := Checked.FSRev.RFlowCells.pos_after (β := -1 / 10) (by norm_num) C hb hs hq0
  have A' := Checked.FSRev.RFlowCells.shift_deriv hs A
  have B' := Checked.FSRev.RFlowCells.shift_deriv hs B
  have C' := Checked.FSRev.RFlowCells.shift_deriv hs C
  refine ⟨fun x => Real.sqrt 10 * (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).1,
    fun x => (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).2.1,
    fun x => (flow a ((x + Real.sqrt 10 * t) / Real.sqrt 10)).2.2 / Real.sqrt 10,
    A', B', C', ?_, Checked.FSRev.RFlowCells.shift_lim _ hlim, ?_, ?_⟩
  · show Real.sqrt 10 * (flow a ((0 + Real.sqrt 10 * t) / Real.sqrt 10)).1 = 0
    rw [zero_add, hst, hz, mul_zero]
  · intro η hη
    exact hpos (η + Real.sqrt 10 * t) (by linarith [mem_Ici.1 hη])
  · have e : (flow a ((0 + Real.sqrt 10 * t) / Real.sqrt 10)).2.2 / Real.sqrt 10 = (flow a t).2.2 / Real.sqrt 10 := by
      rw [zero_add, hst]
    intro h2
    beta_reduce at h2
    rw [e] at h2
    have hr : Real.sqrt 10 < (31623 / 10000 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    rw [div_lt_iff₀ hc] at h2
    nlinarith

end Checked.Trust.NCAB
