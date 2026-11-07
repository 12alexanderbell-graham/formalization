import Checked.Math.GCerts
import Checked.Math.GCellQ
import Checked.Math.GQData

/-! Gelfand problem, `GChain`: (generated certificates; promoted verbatim from `Work/Math/GChain.lean`). Promoted from `Work/Math/GChain.lean`. -/

namespace Checked.Math.GCerts
open Set Checked.Sim Checked.Math.LECell Checked.Math.GCell Checked.Math.GHelp Checked.Math.GCellQ

/-- Chaining of the start and all cells. -/
theorem chain {w φ : ℝ → ℝ} (hw : ∀ s ∈ Icc (0 : ℝ) (41 / 10), HasDerivWithinAt w (φ s) (Icc 0 (41 / 10)) s) (hφ0 : ContinuousWithinAt φ (Icc 0 (41 / 10)) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) (41 / 10),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 (41 / 10)) s)
    (h0 : w 0 = 0) :
    (∀ t ∈ Ioc (0 : ℝ) (3 : ℝ), 0 < 2 + t * φ t) ∧ (∀ t ∈ Icc (3 : ℝ) (814299369/200000000 : ℝ), 0 < φ t + t * Real.exp (w t)) ∧
      |Real.exp (w (1017874211/250000000 : ℝ)) - (1001983101246205873/5000000000000000000 : ℝ)| ≤ (31316544345759/10000000000000000000000000 : ℝ) ∧ |φ (1017874211/250000000 : ℝ) - (-3070123956454913517/6250000000000000000 : ℝ)| ≤ (31316544345759/10000000000000000000000000 : ℝ) ∧
      |φ (814299369/200000000 : ℝ) - (-24560991649594292929/50000000000000000000 : ℝ)| ≤ (156582722125403/50000000000000000000000000 : ℝ) := by
  obtain ⟨n0, a0', b0'⟩ := startI hw hφ0 hφ h0
  have hX : ((41/10 : ℚ) : ℝ) = 41 / 10 := by norm_num
  have hE : ∀ t ∈ Icc (0 : ℝ) ((41/10 : ℚ) : ℝ),
      HasDerivWithinAt (fun s => Real.exp (w s)) (Real.exp (w t) * φ t) (Icc 0 ((41/10 : ℚ) : ℝ)) t := by
    rw [hX]; exact fun t ht => exp_sol (hw t ht)
  have hφ' : ∀ t ∈ Ioc (0 : ℝ) ((41/10 : ℚ) : ℝ),
      HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) (Icc 0 ((41/10 : ℚ) : ℝ)) t := by
    rw [hX]; exact hφ
  have p0 : (0 : ℝ) < (GQData.c0.t0 : ℝ) := by rw [GQData.c0_t0]; norm_num
  have a0 : |Real.exp (w (GQData.c0.t0 : ℝ)) - ((GQData.c0.pe.headD 0 : ℚ) : ℝ)| ≤ (GQData.c0.δ : ℝ) := by
    rw [GQData.c0_t0, GQData.c0_pe, GQData.c0_δ]; push_cast; norm_num at a0' ⊢; exact a0'
  have b0 : |φ (GQData.c0.t0 : ℝ) - ((GQData.c0.pp.headD 0 : ℚ) : ℝ)| ≤ (GQData.c0.δ : ℝ) := by
    rw [GQData.c0_t0, GQData.c0_pp, GQData.c0_δ]; push_cast; norm_num at b0' ⊢; exact b0'
  have g0 : ∀ t ∈ Ioc (0 : ℝ) (GQData.c0.t0 : ℝ), Inv false (fun s => Real.exp (w s)) φ t := by
    rw [GQData.c0_t0]; push_cast; norm_num at n0 ⊢; exact n0
  obtain ⟨o1, i1, a1, b1⟩ := seg_q _ _ _ GQData.seg0_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a0 b0
  have g1 := ioc_glue g0 i1
  obtain ⟨o2, i2, a2, b2⟩ := seg_q _ _ _ GQData.seg1_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a1 b1
  have g2 := ioc_glue g1 i2
  obtain ⟨o3, i3, a3, b3⟩ := seg_q _ _ _ GQData.seg2_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a2 b2
  have g3 := ioc_glue g2 i3
  obtain ⟨o4, i4, a4, b4⟩ := seg_q _ _ _ GQData.seg3_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a3 b3
  have g4 := ioc_glue g3 i4
  obtain ⟨o5, i5, a5, b5⟩ := seg_q _ _ _ GQData.seg4_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a4 b4
  have g5 := ioc_glue g4 i5
  obtain ⟨o6, i6, a6, b6⟩ := seg_q _ _ _ GQData.seg5_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a5 b5
  have g6 := ioc_glue g5 i6
  obtain ⟨o7, i7, a7, b7⟩ := seg_q _ _ _ GQData.seg6_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a6 b6
  rw [GQData.c80_t0] at i7
  push_cast at i7
  have h7 := i7
  obtain ⟨iE, aE, bE⟩ := end_q _ _ GQData.last_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a7 b7
  rw [GQData.c80_t0] at g6
  rw [GQData.c91_t0] at h7 iE
  have hB := icc_glue h7 iE
  rw [GQData.c91_t0, GQData.c91_pe, GQData.c91_δ] at a7
  rw [GQData.c91_t0, GQData.c91_pp, GQData.c91_δ] at b7
  push_cast at g6 hB a7 b7 bE
  refine ⟨fun t ht => g6 t ht, fun t ht => hB t ht, a7, b7, bE⟩

end Checked.Math.GCerts
