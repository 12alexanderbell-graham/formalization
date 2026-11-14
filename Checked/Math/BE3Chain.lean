import Checked.Math.BE3Data

/-! Bonnor–Ebert sphere, `BE3Chain`: the one-sided cells of `BE3Data` chained along every solution of the homology system that starts in the first cell's input box: the sign of 2u − v up to the bracket of the third maximum of the mass, the sign of its derivative and a window of u on that bracket, the sign of 2u − v after it, and the state at the end radius. Promoted from `Work/Math/BE3Chain.lean`. -/

namespace Checked.Math.BE3Chain
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.BEOCell Checked.Math.BE3Data
open Checked.Math.GCellQ (lo hi lo_le le_hi)

set_option maxHeartbeats 8000000 in
theorem chain {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (20000 : ℝ) 300000,
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ)) t)
    (hv : ∀ t ∈ Icc (20000 : ℝ) 300000,
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ)) t)
    (h0 : |u 20000 - 1005687661 / 1000000000| ≤ 2 / 10000000)
    (h0' : |v 20000 - 1989078226 / 1000000000| ≤ 2 / 10000000) :
    (∀ t ∈ Icc (20000 : ℝ) (84497), 0 < 2 * u t - v t) ∧
    (∀ t ∈ Icc (84497 : ℝ) (84516),
      6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t < 0 ∧ (10018942 / 10000000 : ℝ) ≤ u t ∧ u t ≤ 10018978 / 10000000) ∧
    (∀ t ∈ Icc (84516 : ℝ) 300000, 2 * u t - v t < 0) ∧
    |u 300000 - 998005545 / 1000000000| ≤ 4 / 10000000 ∧ |v 300000 - 2002054156 / 1000000000| ≤ 4 / 10000000 := by
  have hX : ((300000 : ℚ) : ℝ) = 300000 := by norm_num
  have hL : ((20000 : ℚ) : ℝ) = 20000 := by norm_num
  have hu' : ∀ t ∈ Icc (c0.t0 : ℝ) ((300000 : ℚ) : ℝ),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ)) t := by
    rw [hX, show c0.t0 = 20000 from rfl]; push_cast; exact hu
  have hv' : ∀ t ∈ Icc (c0.t0 : ℝ) ((300000 : ℚ) : ℝ),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ)) t := by
    rw [hX, show c0.t0 = 20000 from rfl]; push_cast; exact hv
  have a0 : Nw (u (c0.t0 : ℝ) - ((c0.pu.headD 0 : ℚ) : ℝ)) (v (c0.t0 : ℝ) - ((c0.pv.headD 0 : ℚ) : ℝ)) ≤ (c0.δ : ℝ) ^ 2 := by
    rw [show c0.t0 = 20000 from rfl, show c0.pu.headD 0 = 1005687661 / 1000000000 from rfl,
      show c0.pv.headD 0 = 1989078226 / 1000000000 by decide +kernel, show c0.δ = 8 / 10000000 by decide +kernel]
    push_cast
    exact start_box h0 h0' (by norm_num) (by norm_num)
  have p0 : (c0.t0 : ℝ) ≤ (c0.t0 : ℝ) := le_rfl
  obtain ⟨o0, i0, a1⟩ := seg_q _ _ _ s0_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p0], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p0], ht.2⟩) a0
  have p1 := p0.trans o0
  obtain ⟨o1, i1, a2⟩ := seg_q _ _ _ s1_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p1], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p1], ht.2⟩) a1
  have p2 := p1.trans o1
  obtain ⟨o2, i2, a3⟩ := seg_q _ _ _ s2_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p2], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p2], ht.2⟩) a2
  have p3 := p2.trans o2
  obtain ⟨o3, i3, a4⟩ := seg_q _ _ _ s3_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p3], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p3], ht.2⟩) a3
  have p4 := p3.trans o3
  obtain ⟨o4, i4, a5⟩ := seg_q _ _ _ s4_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p4], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p4], ht.2⟩) a4
  have p5 := p4.trans o4
  obtain ⟨o5, i5, a6⟩ := seg_q _ _ _ s5_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p5], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p5], ht.2⟩) a5
  have p6 := p5.trans o5
  obtain ⟨o6, i6, a7⟩ := seg_q _ _ _ s6_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p6], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p6], ht.2⟩) a6
  have p7 := p6.trans o6
  obtain ⟨o7, i7, a8⟩ := seg_q _ _ _ s7_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p7], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p7], ht.2⟩) a7
  have p8 := p7.trans o7
  obtain ⟨i8, kU, kV⟩ := end_q _ _ s8_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p8], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p8], ht.2⟩) a8
  have G0 := i0
  have G0 := Checked.Math.GCellQ.icc_glue G0 i1
  have G0 := Checked.Math.GCellQ.icc_glue G0 i2
  have G0 := Checked.Math.GCellQ.icc_glue G0 i3
  have G1 := i4
  have G2 := i5
  have G2 := Checked.Math.GCellQ.icc_glue G2 i6
  have G2 := Checked.Math.GCellQ.icc_glue G2 i7
  have G2 := Checked.Math.GCellQ.icc_glue G2 i8
  have e0 : (c0.t0 : ℝ) = 20000 := by rw [show c0.t0 = 20000 from rfl]; norm_num
  have e1 : (c40.t0 : ℝ) = 84497 := by rw [show c40.t0 = 84497 from rfl]; norm_num
  have e2 : (c41.t0 : ℝ) = 84516 := by rw [show c41.t0 = 84516 from rfl]; norm_num
  -- the bracket cell of the third maximum: u window
  have hok := (show cellOK (20000 : ℚ) 300000 4 c40 = true by decide +kernel)
  have hok1 : decide (CellProp 20000 300000 c40) = true := by
    simp only [cellOK, Bool.and_eq_true] at hok; exact hok.1
  have hT : ((c40.t0 : ℚ) : ℝ) + ((c40.h : ℚ) : ℝ) ≤ ((300000 : ℚ) : ℝ) := by
    exact_mod_cast (show c40.t0 + c40.h ≤ 300000 by decide +kernel)
  have pb := p4
  have hub : ∀ t ∈ Icc (c40.t0 : ℝ) (c40.t0 + c40.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ)) t := fun t ht =>
    hu' t ⟨by linarith [ht.1, pb], by linarith [ht.2, hT]⟩
  have hvb : ∀ t ∈ Icc (c40.t0 : ℝ) (c40.t0 + c40.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ)) t := fun t ht =>
    hv' t ⟨by linarith [ht.1, pb], by linarith [ht.2, hT]⟩
  have hcq := (cell_q c40 hok1 hub hvb a4).1
  have eh : (c40.t0 : ℝ) + c40.h = 84516 := by
    rw [show c40.t0 = 84497 from rfl, show c40.h = 84516 - 84497 by decide +kernel]; norm_num
  have bu := of_decide_eq_true br_u
  have bu1 : ((10018942 / 10000000 : ℚ) : ℝ) ≤ ((lo c40.pu c40.h - c40.B : ℚ) : ℝ) := by exact_mod_cast bu.1
  have bu2 : ((hi c40.pu c40.h + c40.B : ℚ) : ℝ) ≤ ((10018978 / 10000000 : ℚ) : ℝ) := by exact_mod_cast bu.2
  push_cast at bu1 bu2
  rw [e0] at G0
  rw [hX] at G2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; exact G0 t ⟨ht.1, by rw [e1]; exact ht.2⟩
  · intro t ht
    have ht' : t ∈ Icc (c40.t0 : ℝ) (c40.t0 + c40.h) := ⟨by rw [e1]; exact ht.1, by rw [eh]; exact ht.2⟩
    have hN := hcq t ht'
    obtain ⟨c1, -⟩ := cell_box' c40 hok1 ht' hN
    have l1 := lo_le c40.pu (h := c40.h) (σ := t - c40.t0) (by linarith [ht'.1]) (by linarith [ht'.2])
    have l2 := le_hi c40.pu (h := c40.h) (σ := t - c40.t0) (by linarith [ht'.1]) (by linarith [ht'.2])
    have c1' := abs_le.1 c1
    rw [e1, e2] at G1
    exact ⟨G1 t ht, by linarith [c1'.1], by linarith [c1'.2]⟩
  · intro t ht; rw [e2] at G2; exact G2 t ht
  · push_cast at kU; norm_num at kU ⊢; exact kU
  · push_cast at kV; norm_num at kV ⊢; exact kV

end Checked.Math.BE3Chain
