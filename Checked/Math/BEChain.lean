import Checked.Math.BEStart
import Checked.Math.BEQData

/-! Bonnor–Ebert sphere, `BEChain`: the cells chained from the start: the sign of exp w minus half the square of w' on each side of the bracket of the critical radius, and the enclosure on the bracket cell. Promoted from `Work/Math/BEChain.lean`. -/

namespace Checked.Math.BEChain
open Set Checked.Sim Checked.Math.GCell Checked.Math.GCellQ Checked.Math.BECellQ Checked.Math.BEQData

theorem chain {w φ : ℝ → ℝ} (hw : ∀ s ∈ Icc (0 : ℝ) 7, HasDerivWithinAt w (φ s) (Icc 0 7) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 7) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) 7,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 7) s)
    (h0 : w 0 = 0) :
    (∀ t ∈ Icc (1 / 64 : ℝ) (80634393/12500000 : ℝ), BInv 1 (fun s => Real.exp (w s)) φ t) ∧
    (∀ t ∈ Icc (80634393/12500000 : ℝ) (12901503/2000000 : ℝ), |Real.exp (w t) - evalQ c332.pe (t - (80634393/12500000 : ℝ))| ≤ c332.B ∧
      |φ t - evalQ c332.pp (t - (80634393/12500000 : ℝ))| ≤ c332.B) ∧
    (∀ t ∈ Icc (12901503/2000000 : ℝ) 7, BInv 2 (fun s => Real.exp (w s)) φ t) := by
  obtain ⟨-, a0', b0'⟩ := Checked.Math.BEStart.startBE hw hφ0 hφ h0
  have hX : ((7 : ℚ) : ℝ) = 7 := by norm_num
  have hE : ∀ t ∈ Icc (0 : ℝ) ((7 : ℚ) : ℝ),
      HasDerivWithinAt (fun s => Real.exp (w s)) (Real.exp (w t) * φ t) (Icc 0 ((7 : ℚ) : ℝ)) t := by
    rw [hX]; exact fun t ht => exp_sol (hw t ht)
  have hφ' : ∀ t ∈ Icc (c0.t0 : ℝ) ((7 : ℚ) : ℝ),
      HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) (Icc 0 ((7 : ℚ) : ℝ)) t := by
    rw [hX, c0_t0]; push_cast
    exact fun t ht => hφ t ⟨by linarith [ht.1], ht.2⟩
  have hc0 : (0 : ℝ) < (c0.t0 : ℝ) := by rw [c0_t0]; norm_num
  have a0 : |Real.exp (w (c0.t0 : ℝ)) - ((c0.pe.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [c0_t0, c0_pe, c0_δ]; push_cast; norm_num at a0' ⊢; exact a0'
  have b0 : |φ (c0.t0 : ℝ) - ((c0.pp.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [c0_t0, c0_pp, c0_δ]; push_cast; norm_num at b0' ⊢; exact b0'
  have p0 : (c0.t0 : ℝ) ≤ (c0.t0 : ℝ) := le_rfl
  obtain ⟨o0, i0, a1, b1⟩ := bseg_q _ _ _ inc0_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p0, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p0], ht.2⟩) a0 b0
  have p1 := p0.trans o0
  have g0 := i0
  obtain ⟨o1, i1, a2, b2⟩ := bseg_q _ _ _ inc1_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p1, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p1], ht.2⟩) a1 b1
  have p2 := p1.trans o1
  have g1 := icc_glue g0 i1
  obtain ⟨o2, i2, a3, b3⟩ := bseg_q _ _ _ inc2_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p2, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p2], ht.2⟩) a2 b2
  have p3 := p2.trans o2
  have g2 := icc_glue g1 i2
  obtain ⟨o3, i3, a4, b4⟩ := bseg_q _ _ _ inc3_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p3, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p3], ht.2⟩) a3 b3
  have p4 := p3.trans o3
  have g3 := icc_glue g2 i3
  obtain ⟨o4, i4, a5, b5⟩ := bseg_q _ _ _ inc4_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p4, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p4], ht.2⟩) a4 b4
  have p5 := p4.trans o4
  have g4 := icc_glue g3 i4
  obtain ⟨o5, i5, a6, b6⟩ := bseg_q _ _ _ inc5_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p5, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p5], ht.2⟩) a5 b5
  have p6 := p5.trans o5
  have g5 := icc_glue g4 i5
  obtain ⟨o6, i6, a7, b7⟩ := bseg_q _ _ _ inc6_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p6, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p6], ht.2⟩) a6 b6
  have p7 := p6.trans o6
  have g6 := icc_glue g5 i6
  obtain ⟨o7, i7, a8, b8⟩ := bseg_q _ _ _ inc7_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p7, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p7], ht.2⟩) a7 b7
  have p8 := p7.trans o7
  have g7 := icc_glue g6 i7
  obtain ⟨o8, i8, a9, b9⟩ := bseg_q _ _ _ inc8_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p8, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p8], ht.2⟩) a8 b8
  have p9 := p8.trans o8
  have g8 := icc_glue g7 i8
  obtain ⟨o9, i9, a10, b10⟩ := bseg_q _ _ _ inc9_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p9, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p9], ht.2⟩) a9 b9
  have p10 := p9.trans o9
  have g9 := icc_glue g8 i9
  obtain ⟨o10, i10, a11, b11⟩ := bseg_q _ _ _ inc10_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p10, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p10], ht.2⟩) a10 b10
  have p11 := p10.trans o10
  have g10 := icc_glue g9 i10
  obtain ⟨o11, i11, a12, b12⟩ := bseg_q _ _ _ inc11_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p11, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p11], ht.2⟩) a11 b11
  have p12 := p11.trans o11
  have g11 := icc_glue g10 i11
  obtain ⟨o12, i12, a13, b13⟩ := bseg_q _ _ _ inc12_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p12, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p12], ht.2⟩) a12 b12
  have p13 := p12.trans o12
  have g12 := icc_glue g11 i12
  obtain ⟨o13, i13, a14, b14⟩ := bseg_q _ _ _ inc13_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p13, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p13], ht.2⟩) a13 b13
  have p14 := p13.trans o13
  have g13 := icc_glue g12 i13
  obtain ⟨o14, i14, a15, b15⟩ := bseg_q _ _ _ inc14_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p14, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p14], ht.2⟩) a14 b14
  have p15 := p14.trans o14
  have g14 := icc_glue g13 i14
  obtain ⟨o15, i15, a16, b16⟩ := bseg_q _ _ _ inc15_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p15, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p15], ht.2⟩) a15 b15
  have p16 := p15.trans o15
  have g15 := icc_glue g14 i15
  obtain ⟨o16, i16, a17, b17⟩ := bseg_q _ _ _ inc16_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p16, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p16], ht.2⟩) a16 b16
  have p17 := p16.trans o16
  have g16 := icc_glue g15 i16
  obtain ⟨o17, i17, a18, b18⟩ := bseg_q _ _ _ inc17_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p17, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p17], ht.2⟩) a17 b17
  have p18 := p17.trans o17
  have g17 := icc_glue g16 i17
  obtain ⟨o18, i18, a19, b19⟩ := bseg_q _ _ _ inc18_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p18, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p18], ht.2⟩) a18 b18
  have p19 := p18.trans o18
  have g18 := icc_glue g17 i18
  obtain ⟨o19, i19, a20, b20⟩ := bseg_q _ _ _ inc19_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p19, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p19], ht.2⟩) a19 b19
  have p20 := p19.trans o19
  have g19 := icc_glue g18 i19
  obtain ⟨o20, i20, a21, b21⟩ := bseg_q _ _ _ inc20_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p20, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p20], ht.2⟩) a20 b20
  have p21 := p20.trans o20
  have g20 := icc_glue g19 i20
  obtain ⟨o21, i21, a22, b22⟩ := bseg_q _ _ _ inc21_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p21, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p21], ht.2⟩) a21 b21
  have p22 := p21.trans o21
  have g21 := icc_glue g20 i21
  obtain ⟨o22, i22, a23, b23⟩ := bseg_q _ _ _ inc22_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p22, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p22], ht.2⟩) a22 b22
  have p23 := p22.trans o22
  have g22 := icc_glue g21 i22
  -- the bracket cell c332
  have gok : decide (CellProp (7 : ℚ) c332) = true := gap_ok
  have gok0 : bcellOK (7 : ℚ) 0 c332 = true := by
    unfold bcellOK; rw [gap_ok, Bool.true_and]; decide
  obtain ⟨-, kg2, kg3⟩ := bcell_basic c332 gok0
  have kg2' : ((c332.t0 + c332.h : ℚ) : ℝ) ≤ ((7 : ℚ) : ℝ) := by exact_mod_cast kg2
  push_cast at kg2'
  have hgE : ∀ t ∈ Icc (c332.t0 : ℝ) (c332.t0 + c332.h),
      HasDerivWithinAt (fun s => Real.exp (w s)) (Real.exp (w t) * φ t) (Icc 0 ((7 : ℚ) : ℝ)) t :=
    fun t ht => hE t ⟨by linarith [ht.1, p23, hc0], by linarith [ht.2]⟩
  have hgφ : ∀ t ∈ Icc (c332.t0 : ℝ) (c332.t0 + c332.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) (Icc 0 ((7 : ℚ) : ℝ)) t :=
    fun t ht => hφ' t ⟨by linarith [ht.1, p23], by linarith [ht.2]⟩
  have hgap := cell_q c332 gok hgE hgφ a23 b23
  have hgf := bcell_facts c332 gok0 hgE hgφ a23 b23
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true gap_link
  have he : ((c332.t0 + c332.h : ℚ) : ℝ) = (c333.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hgf
  have kE' : |((Checked.Sim.QPoly.qeval c332.pe c332.h : ℚ) : ℝ) - ((c333.pe.headD 0 : ℚ) : ℝ)| + c332.B ≤ c333.δ := by
    exact_mod_cast kE
  have kφ' : |((Checked.Sim.QPoly.qeval c332.pp c332.h : ℚ) : ℝ) - ((c333.pp.headD 0 : ℚ) : ℝ)| + c332.B ≤ c333.δ := by
    exact_mod_cast kφ
  have ad := abs_link hgf.2.1 kE'
  have bd := abs_link hgf.2.2 kφ'
  have hgh : (0 : ℝ) < c332.h := by exact_mod_cast kg3
  have q23 : (c0.t0 : ℝ) ≤ c333.t0 := by rw [← he]; linarith [p23]
  obtain ⟨o24, i24, a25, b25⟩ := bseg_q _ _ _ dec0_ok
    (fun t ht => hE t ⟨by linarith [ht.1, q23, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, q23], ht.2⟩) ad bd
  have p25 := q23.trans o24
  have g24 := i24
  obtain ⟨o25, i25, a26, b26⟩ := bseg_q _ _ _ dec1_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p25, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p25], ht.2⟩) a25 b25
  have p26 := p25.trans o25
  have g25 := icc_glue g24 i25
  obtain ⟨o26, i26, a27, b27⟩ := bseg_q _ _ _ dec2_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p26, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p26], ht.2⟩) a26 b26
  have p27 := p26.trans o26
  have g26 := icc_glue g25 i26
  have i27 := bend_q _ _ dec3_ok
    (fun t ht => hE t ⟨by linarith [ht.1, p27, hc0], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1, p27], ht.2⟩) a27 b27
  have g27 := icc_glue g26 i27
  rw [c0_t0] at g22
  rw [c332_t0] at g22
  rw [c333_t0] at g27
  push_cast at g22 g27
  refine ⟨fun t ht => g22 t ht, fun t ht => ?_, fun t ht => g27 t ht⟩
  have hh : (c332.t0 : ℝ) + c332.h = (12901503/2000000 : ℝ) := by rw [he, c333_t0]; push_cast; norm_num
  have ht' : t ∈ Icc (c332.t0 : ℝ) (c332.t0 + c332.h) := by
    rw [hh, c332_t0]; push_cast; exact ht
  have := hgap t ht'
  rw [c332_t0] at this
  push_cast at this
  exact this

end Checked.Math.BEChain
