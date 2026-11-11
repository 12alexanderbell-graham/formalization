import Work.FSRev.R1988Printed

/-! Falkner–Skan at the scaled coefficient 2500/497 with the printed reversed wall value: the end state of
the printed-value chain at t = 4 (0 < f ≤ 4, |p − 1| ≤ 1/2, |q| ≤ 1/2), read from the range of the last
checked cell. Run 2026-11-11T1828Z. -/

namespace Work.FSRev.R1988PrintedEnd
open Set Checked.Sim Checked.Sim.QPoly Checked.FSSep.SCellWC Checked.FSNeg.NBase Checked.FSSep.SBase
  Work.FSAtt.ABase Work.FSRev.RBase Work.FSRev.RCell Work.FSRev.RIdent Work.FSRev.R1988Printed

/-- On a checked cell, the enclosed solution lies in the cell's ranges. -/
theorem cell_range {K T : ℚ} (c : Cell) (hok : cellOK K T c = true) {g p q : ℝ → ℝ}
    (hs : SolC (K : ℝ) T c.t0 g p q) (h0 : InBox c g p q) (t : ℝ) (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h)) :
    ((glo c - c.r1 : ℚ) : ℝ) ≤ g t ∧ g t ≤ ((ghi c + c.r1 : ℚ) : ℝ) ∧
    ((plo c - c.r2 : ℚ) : ℝ) ≤ p t ∧ p t ≤ ((phi c + c.r2 : ℚ) : ℝ) ∧
    ((qlo c - c.B : ℚ) : ℝ) ≤ q t ∧ q t ≤ ((qhi c + c.B : ℚ) : ℝ) := by
  obtain ⟨b1, b2, b3⟩ := encl c hok hs h0 t ht
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have lg := lower_q c.pg (h := c.h) hσ.1 hσ.2
  have ug := upper_q c.pg (h := c.h) hσ.1 hσ.2
  have lp := lower_q c.pp (h := c.h) hσ.1 hσ.2
  have up := upper_q c.pp (h := c.h) hσ.1 hσ.2
  have lq := lower_q c.pq (h := c.h) hσ.1 hσ.2
  have uq := upper_q c.pq (h := c.h) hσ.1 hσ.2
  simp only [glo, ghi, plo, phi, qlo, qhi]
  push_cast at lg ug lp up lq uq ⊢
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem seg16e_ok : chainS (2500/497 : ℚ) (4 : ℚ) sideT (fun e => linkOK e c133) [c128, c129, c130, c131, c132] = true := by
  decide +kernel

theorem c133_ok : cellOK (2500/497 : ℚ) (4 : ℚ) c133 = true := by
  decide +kernel

theorem range_ok : (0 : ℚ) < glo c133 - c133.r1 ∧ ghi c133 + c133.r1 ≤ 4 ∧ 1 / 2 ≤ plo c133 - c133.r2 ∧
    phi c133 + c133.r2 ≤ 3 / 2 ∧ -1 / 2 ≤ qlo c133 - c133.B ∧ qhi c133 + c133.B ≤ 1 / 2 := by
  decide +kernel

/-- End state at t = 4 of every clamped solution from the printed reversed wall value. -/
theorem endState {Y : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc (0 : ℝ) (4 : ℝ), HasDerivWithinAt Y (vS (2500 / 497 : ℝ) t (Y t)) (Icc 0 (4 : ℝ)) t)
    {α : ℝ} (h0 : Y 0 = (0, 0, α)) (hα : |α - (-11568396030579 / 1000000000000000)| ≤ 1 / 100000000000000) :
    0 < (Y 4).1 ∧ (Y 4).1 ≤ 4 ∧ |(Y 4).2.1 - 1| ≤ 1 / 2 ∧ |(Y 4).2.2| ≤ 1 / 2 := by
  have hX : (((4 : ℚ) : ℚ) : ℝ) = (4 : ℝ) := by norm_num
  have hK : (((2500/497 : ℚ) : ℚ) : ℝ) = (2500 / 497 : ℝ) := by norm_num
  have hs : SolC (((2500/497 : ℚ) : ℚ) : ℝ) (((4 : ℚ) : ℚ) : ℝ) 0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    rw [hX, hK]
    exact ⟨fun t ht => (hY t ht).fst, fun t ht => (hY t ht).snd.fst, fun t ht => (hY t ht).snd.snd⟩
  have z0 : ((c0.t0 : ℚ) : ℝ) = 0 := by simp [c0]
  have b0 : InBox c0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    unfold InBox; simp only [z0, h0]
    simp only [V, c0, List.headD_cons]; push_cast
    have hα' := abs_le.1 hα
    nlinarith [hα'.1, hα'.2]

  obtain ⟨b1, P0⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c8 [c1, c2, c3, c4, c5, c6, c7] c0 seg0_ok hs b0
  rw [z0] at P0
  obtain ⟨b2, P1⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c16 [c9, c10, c11, c12, c13, c14, c15] c8 seg1_ok hs b1
  have A1 := glue P0 P1
  obtain ⟨b3, P2⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c24 [c17, c18, c19, c20, c21, c22, c23] c16 seg2_ok hs b2
  have A2 := glue A1 P2
  obtain ⟨b4, P3⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c32 [c25, c26, c27, c28, c29, c30, c31] c24 seg3_ok hs b3
  have A3 := glue A2 P3
  obtain ⟨b5, P4⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c40 [c33, c34, c35, c36, c37, c38, c39] c32 seg4_ok hs b4
  have A4 := glue A3 P4
  obtain ⟨b6, P5⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c48 [c41, c42, c43, c44, c45, c46, c47] c40 seg5_ok hs b5
  have A5 := glue A4 P5
  obtain ⟨b7, P6⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c56 [c49, c50, c51, c52, c53, c54, c55] c48 seg6_ok hs b6
  have A6 := glue A5 P6
  obtain ⟨b8, P7⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c64 [c57, c58, c59, c60, c61, c62, c63] c56 seg7_ok hs b7
  have A7 := glue A6 P7
  obtain ⟨b9, P8⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c72 [c65, c66, c67, c68, c69, c70, c71] c64 seg8_ok hs b8
  have A8 := glue A7 P8
  obtain ⟨b10, P9⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c80 [c73, c74, c75, c76, c77, c78, c79] c72 seg9_ok hs b9
  have A9 := glue A8 P9
  obtain ⟨b11, P10⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c88 [c81, c82, c83, c84, c85, c86, c87] c80 seg10_ok hs b10
  have A10 := glue A9 P10
  obtain ⟨b12, P11⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c96 [c89, c90, c91, c92, c93, c94, c95] c88 seg11_ok hs b11
  have A11 := glue A10 P11
  obtain ⟨b13, P12⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c104 [c97, c98, c99, c100, c101, c102, c103] c96 seg12_ok hs b12
  have A12 := glue A11 P12
  obtain ⟨b14, P13⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c112 [c105, c106, c107, c108, c109, c110, c111] c104 seg13_ok hs b13
  have A13 := glue A12 P13
  obtain ⟨b15, P14⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c120 [c113, c114, c115, c116, c117, c118, c119] c112 seg14_ok hs b14
  have A14 := glue A13 P14
  obtain ⟨b16, P15⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c128 [c121, c122, c123, c124, c125, c126, c127] c120 seg15_ok hs b15
  have A15 := glue A14 P15
  obtain ⟨b17, -⟩ := segS_q0 (Φ := PhiS) (fun c hok _ => cell_box_lt c hok) c133 [c129, c130, c131, c132] c128 seg16e_ok hs b16
  have ht0 : ((c133.t0 : ℚ) : ℝ) = 127 / 32 := by norm_num [c133]
  have hth : ((c133.t0 : ℚ) : ℝ) + ((c133.h : ℚ) : ℝ) = 4 := by norm_num [c133]
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := cell_range c133 c133_ok (hs.mono (by rw [ht0]; norm_num)) b17 4
    ⟨by rw [ht0]; norm_num, hth.ge⟩
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := range_ok
  have k1' : ((0 : ℚ) : ℝ) < ((glo c133 - c133.r1 : ℚ) : ℝ) := by exact_mod_cast k1
  have k2' : ((ghi c133 + c133.r1 : ℚ) : ℝ) ≤ ((4 : ℚ) : ℝ) := by exact_mod_cast k2
  have k3' : ((1 / 2 : ℚ) : ℝ) ≤ ((plo c133 - c133.r2 : ℚ) : ℝ) := by exact_mod_cast k3
  have k4' : ((phi c133 + c133.r2 : ℚ) : ℝ) ≤ ((3 / 2 : ℚ) : ℝ) := by exact_mod_cast k4
  have k5' : ((-1 / 2 : ℚ) : ℝ) ≤ ((qlo c133 - c133.B : ℚ) : ℝ) := by exact_mod_cast k5
  have k6' : ((qhi c133 + c133.B : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast k6
  push_cast at k1' k2' k3' k4' k5' k6' r1 r2 r3 r4 r5 r6
  refine ⟨by linarith, by linarith, abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

end Work.FSRev.R1988PrintedEnd
