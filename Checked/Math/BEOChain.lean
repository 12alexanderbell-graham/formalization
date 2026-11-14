import Checked.Math.BEOData

/-! Bonnor–Ebert sphere, `BEOChain`: the one-sided cells of `BEOData` chained along every solution of the homology system that starts in the first cell's input box: the sign of 2u − v up to the bracket of the second maximum of the mass, the sign of its derivative and a box on that bracket, the sign of 2u − v up to the bracket of the second minimum, the sign of its derivative and a window of u on that bracket, the sign of 2u − v after it, and the state at the end radius. Promoted from `Work/Math/BEOChain.lean`. -/

namespace Checked.Math.BEOChain
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.BEOCell Checked.Math.BEOData
open Checked.Math.GCellQ (lo hi lo_le le_hi)

set_option maxHeartbeats 8000000 in
theorem chain {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (150 : ℝ) 20000,
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((150 : ℚ) : ℝ) ((20000 : ℚ) : ℝ)) t)
    (hv : ∀ t ∈ Icc (150 : ℝ) 20000,
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((150 : ℚ) : ℝ) ((20000 : ℚ) : ℝ)) t)
    (h0 : |u 150 - 2105111091 / 2000000000| ≤ 1 / 5000000)
    (h0' : |v 150 - 2331774279 / 1250000000| ≤ 1 / 5000000) :
    (∀ t ∈ Icc (150 : ℝ) (18344 / 25), 0 < 2 * u t - v t) ∧
    (∀ t ∈ Icc (18344 / 25 : ℝ) (36689 / 50), 6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t < 0 ∧
      (102 / 100 : ℝ) ≤ u t ∧ (204 / 100 : ℝ) ≤ v t) ∧
    (∀ t ∈ Icc (36689 / 50 : ℝ) (15699 / 2), 2 * u t - v t < 0) ∧
    (∀ t ∈ Icc (15699 / 2 : ℝ) (31399 / 4),
      0 < 6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t ∧ (99378175 / 100000000 : ℝ) ≤ u t ∧ u t ≤ 99378323 / 100000000) ∧
    (∀ t ∈ Icc (31399 / 4 : ℝ) 20000, 0 < 2 * u t - v t) ∧
    |u 20000 - 1005687661 / 1000000000| ≤ 2 / 10000000 ∧ |v 20000 - 1989078226 / 1000000000| ≤ 2 / 10000000 := by
  have hX : ((20000 : ℚ) : ℝ) = 20000 := by norm_num
  have hu' : ∀ t ∈ Icc (c0.t0 : ℝ) ((20000 : ℚ) : ℝ),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((150 : ℚ) : ℝ) ((20000 : ℚ) : ℝ)) t := by
    rw [hX, show c0.t0 = 150 from rfl]; push_cast; exact hu
  have hv' : ∀ t ∈ Icc (c0.t0 : ℝ) ((20000 : ℚ) : ℝ),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((150 : ℚ) : ℝ) ((20000 : ℚ) : ℝ)) t := by
    rw [hX, show c0.t0 = 150 from rfl]; push_cast; exact hv
  have a0 : Nw (u (c0.t0 : ℝ) - ((c0.pu.headD 0 : ℚ) : ℝ)) (v (c0.t0 : ℝ) - ((c0.pv.headD 0 : ℚ) : ℝ)) ≤ (c0.δ : ℝ) ^ 2 := by
    rw [show c0.t0 = 150 from rfl, show c0.pu.headD 0 = 2105111091 / 2000000000 from rfl,
      show c0.pv.headD 0 = 2331774279 / 1250000000 from rfl, show c0.δ = 4 / 5000000 by decide +kernel]
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
  obtain ⟨o8, i8, a9⟩ := seg_q _ _ _ s8_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p8], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p8], ht.2⟩) a8
  have p9 := p8.trans o8
  obtain ⟨o9, i9, a10⟩ := seg_q _ _ _ s9_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p9], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p9], ht.2⟩) a9
  have p10 := p9.trans o9
  obtain ⟨o10, i10, a11⟩ := seg_q _ _ _ s10_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p10], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p10], ht.2⟩) a10
  have p11 := p10.trans o10
  obtain ⟨o11, i11, a12⟩ := seg_q _ _ _ s11_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p11], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p11], ht.2⟩) a11
  have p12 := p11.trans o11
  obtain ⟨o12, i12, a13⟩ := seg_q _ _ _ s12_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p12], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p12], ht.2⟩) a12
  have p13 := p12.trans o12
  obtain ⟨o13, i13, a14⟩ := seg_q _ _ _ s13_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p13], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p13], ht.2⟩) a13
  have p14 := p13.trans o13
  obtain ⟨o14, i14, a15⟩ := seg_q _ _ _ s14_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p14], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p14], ht.2⟩) a14
  have p15 := p14.trans o14
  obtain ⟨o15, i15, a16⟩ := seg_q _ _ _ s15_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p15], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p15], ht.2⟩) a15
  have p16 := p15.trans o15
  obtain ⟨o16, i16, a17⟩ := seg_q _ _ _ s16_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p16], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p16], ht.2⟩) a16
  have p17 := p16.trans o16
  obtain ⟨o17, i17, a18⟩ := seg_q _ _ _ s17_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p17], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p17], ht.2⟩) a17
  have p18 := p17.trans o17
  obtain ⟨i18, kU, kV⟩ := end_q _ _ s18_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p18], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p18], ht.2⟩) a18
  have G0 := i0
  have G0 := Checked.Math.GCellQ.icc_glue G0 i1
  have G0 := Checked.Math.GCellQ.icc_glue G0 i2
  have G0 := Checked.Math.GCellQ.icc_glue G0 i3
  have G0 := Checked.Math.GCellQ.icc_glue G0 i4
  have G1 := i5
  have G2 := i6
  have G2 := Checked.Math.GCellQ.icc_glue G2 i7
  have G2 := Checked.Math.GCellQ.icc_glue G2 i8
  have G2 := Checked.Math.GCellQ.icc_glue G2 i9
  have G2 := Checked.Math.GCellQ.icc_glue G2 i10
  have G2 := Checked.Math.GCellQ.icc_glue G2 i11
  have G2 := Checked.Math.GCellQ.icc_glue G2 i12
  have G2 := Checked.Math.GCellQ.icc_glue G2 i13
  have G3 := i14
  have G4 := i15
  have G4 := Checked.Math.GCellQ.icc_glue G4 i16
  have G4 := Checked.Math.GCellQ.icc_glue G4 i17
  have G4 := Checked.Math.GCellQ.icc_glue G4 i18
  have e0 : (c0.t0 : ℝ) = 150 := by rw [show c0.t0 = 150 from rfl]; norm_num
  have e1 : (c44.t0 : ℝ) = 18344 / 25 := by rw [show c44.t0 = 18344 / 25 from rfl]; norm_num
  have e2 : (c45.t0 : ℝ) = 36689 / 50 := by rw [show c45.t0 = 36689 / 50 from rfl]; norm_num
  have e3 : (c119.t0 : ℝ) = 15699 / 2 := by rw [show c119.t0 = 15699 / 2 from rfl]; norm_num
  have e4 : (c120.t0 : ℝ) = 31399 / 4 := by rw [show c120.t0 = 31399 / 4 from rfl]; norm_num
  -- the bracket cell of the second minimum: u window
  have hok := (show cellOK (150 : ℚ) 20000 3 c119 = true by decide +kernel)
  have hok1 : decide (CellProp 150 20000 c119) = true := by
    simp only [cellOK, Bool.and_eq_true] at hok; exact hok.1
  have hT : ((c119.t0 : ℚ) : ℝ) + ((c119.h : ℚ) : ℝ) ≤ ((20000 : ℚ) : ℝ) := by
    exact_mod_cast (show c119.t0 + c119.h ≤ 20000 by decide +kernel)
  have pb := p14
  have hub : ∀ t ∈ Icc (c119.t0 : ℝ) (c119.t0 + c119.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((150 : ℚ) : ℝ) ((20000 : ℚ) : ℝ)) t := fun t ht =>
    hu' t ⟨by linarith [ht.1, pb], by linarith [ht.2, hT]⟩
  have hvb : ∀ t ∈ Icc (c119.t0 : ℝ) (c119.t0 + c119.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((150 : ℚ) : ℝ) ((20000 : ℚ) : ℝ)) t := fun t ht =>
    hv' t ⟨by linarith [ht.1, pb], by linarith [ht.2, hT]⟩
  have hcq := (cell_q c119 hok1 hub hvb a14).1
  have eh : (c119.t0 : ℝ) + c119.h = 31399 / 4 := by
    rw [show c119.t0 = 15699 / 2 from rfl, show c119.h = 31399 / 4 - 15699 / 2 by decide +kernel]; norm_num
  have bu := of_decide_eq_true br_u
  have bu1 : ((99378175 / 100000000 : ℚ) : ℝ) ≤ ((lo c119.pu c119.h - c119.B : ℚ) : ℝ) := by exact_mod_cast bu.1
  have bu2 : ((hi c119.pu c119.h + c119.B : ℚ) : ℝ) ≤ ((99378323 / 100000000 : ℚ) : ℝ) := by exact_mod_cast bu.2
  push_cast at bu1 bu2
  rw [e0] at G0
  rw [hX] at G4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; exact G0 t ⟨ht.1, by rw [e1]; exact ht.2⟩
  · intro t ht
    have hok3 := (show cellOK (150 : ℚ) 20000 4 c44 = true by decide +kernel)
    have hok31 : decide (CellProp 150 20000 c44) = true := by
      simp only [cellOK, Bool.and_eq_true] at hok3; exact hok3.1
    have hT3 : ((c44.t0 : ℚ) : ℝ) + ((c44.h : ℚ) : ℝ) ≤ ((20000 : ℚ) : ℝ) := by
      exact_mod_cast (show c44.t0 + c44.h ≤ 20000 by decide +kernel)
    have pb3 := p5
    have hcq3 := (cell_q c44 hok31 (fun t ht => hu' t ⟨by linarith [ht.1, pb3], by linarith [ht.2, hT3]⟩)
      (fun t ht => hv' t ⟨by linarith [ht.1, pb3], by linarith [ht.2, hT3]⟩) a5).1
    have eh3 : (c44.t0 : ℝ) + c44.h = 36689 / 50 := by
      rw [show c44.t0 = 18344 / 25 from rfl, show c44.h = 36689 / 50 - 18344 / 25 by decide +kernel]; norm_num
    have ht' : t ∈ Icc (c44.t0 : ℝ) (c44.t0 + c44.h) := ⟨by rw [e1]; exact ht.1, by rw [eh3]; exact ht.2⟩
    obtain ⟨-, -, b1, -, b3, -⟩ := cell_box' c44 hok31 ht' (hcq3 t ht')
    have bb := of_decide_eq_true br3_box
    have bb1 : ((102 / 100 : ℚ) : ℝ) ≤ ((c44.UL : ℚ) : ℝ) := by exact_mod_cast bb.1
    have bb2 : ((204 / 100 : ℚ) : ℝ) ≤ ((c44.VL : ℚ) : ℝ) := by exact_mod_cast bb.2
    push_cast at bb1 bb2
    rw [e1, e2] at G1
    exact ⟨G1 t ht, by linarith, by linarith⟩
  · intro t ht; rw [e2, e3] at G2; exact G2 t ht
  · intro t ht
    have ht' : t ∈ Icc (c119.t0 : ℝ) (c119.t0 + c119.h) := ⟨by rw [e3]; exact ht.1, by rw [eh]; exact ht.2⟩
    have hN := hcq t ht'
    obtain ⟨c1, -⟩ := cell_box' c119 hok1 ht' hN
    have l1 := lo_le c119.pu (h := c119.h) (σ := t - c119.t0) (by linarith [ht'.1]) (by linarith [ht'.2])
    have l2 := le_hi c119.pu (h := c119.h) (σ := t - c119.t0) (by linarith [ht'.1]) (by linarith [ht'.2])
    have c1' := abs_le.1 c1
    rw [e3, e4] at G3
    exact ⟨G3 t ht, by linarith [c1'.1], by linarith [c1'.2]⟩
  · intro t ht; rw [e4] at G4; exact G4 t ht
  · push_cast at kU; norm_num at kU ⊢; exact kU
  · push_cast at kV; norm_num at kV ⊢; exact kV

end Checked.Math.BEOChain
