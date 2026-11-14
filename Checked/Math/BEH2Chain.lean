import Checked.Math.BEH2Data

/-! Bonnor–Ebert sphere, `BEH2Chain`: the cells of `BEH2Data` chained along every solution of the homology system that starts in the first cell's input box: the sign of 2u − v before and after the bracket cell of the second maximum of the mass, the sign of its derivative and a window of u on the bracket cell, and the state at the end radius. Promoted from `Work/Math/BEH2Chain.lean`. -/

namespace Checked.Math.BEH2Chain
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.BEHCell Checked.Math.BEH2Data
open Checked.Math.GCellQ (lo hi lo_le le_hi abs_link icc_glue)

/-- On a cell whose polynomial bound of 6u − 2u² − 3uv + v is negative with room for the enclosure, the
solution has 6u − 2u² − 3uv + v < 0. -/
theorem neg_G {L T : ℚ} (c : Cell) (hok : decide (CellProp L T c) = true)
    (hG : decide (hi (Gp c) c.h + (7 + 7 * c.UH + 3 * c.VH) * c.B < 0) = true) {u v : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h))
    (e1 : |u t - evalQ c.pu (t - c.t0)| ≤ c.B) (e2 : |v t - evalQ c.pv (t - c.t0)| ≤ c.B) :
    6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t < 0 := by
  have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
  have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hB, hUL, hVL⟩ := cell_box c hok ht e1 e2
  have rv : ((hi (Gp c) c.h + (7 + 7 * c.UH + 3 * c.VH) * c.B : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by
    exact_mod_cast of_decide_eq_true hG
  push_cast at rv
  have hl := le_hi (Gp c) hσ0 hσ1
  rw [← Gp_eval] at hl
  set p := evalQ c.pu (t - c.t0)
  set q := evalQ c.pv (t - c.t0)
  have e : (6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t) -
      (6 * p - 2 * p ^ 2 - 3 * (p * q) + q) =
      (6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q) := by ring
  have c1 : |6 - 2 * (u t + p) - 3 * v t| ≤ 6 + 4 * c.UH + 3 * c.VH := by
    rw [abs_le]; constructor <;> linarith
  have c2 : |1 - 3 * p| ≤ 1 + 3 * c.UH := by rw [abs_le]; constructor <;> linarith
  have d : |(6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q)| ≤
      (7 + 7 * c.UH + 3 * c.VH) * c.B := by
    calc _ ≤ |(6 - 2 * (u t + p) - 3 * v t) * (u t - p)| + |(1 - 3 * p) * (v t - q)| :=
          abs_add_le _ _
      _ = |6 - 2 * (u t + p) - 3 * v t| * |u t - p| + |1 - 3 * p| * |v t - q| := by
          rw [abs_mul, abs_mul]
      _ ≤ (6 + 4 * c.UH + 3 * c.VH) * c.B + (1 + 3 * c.UH) * c.B := by
          gcongr <;> linarith [abs_nonneg (6 - 2 * (u t + p) - 3 * v t), abs_nonneg (1 - 3 * p)]
      _ = (7 + 7 * c.UH + 3 * c.VH) * c.B := by ring
  rw [← e] at d
  have := (abs_le.1 d).2
  linarith

theorem br_u : decide ((1020324 / 1000000 : ℚ) ≤ lo c83.pu c83.h - c83.B ∧
    hi c83.pu c83.h + c83.B ≤ 1020415 / 1000000) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem chain {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (150 : ℝ) 2000,
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((150 : ℚ) : ℝ) ((2000 : ℚ) : ℝ)) t)
    (hv : ∀ t ∈ Icc (150 : ℝ) 2000,
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((150 : ℚ) : ℝ) ((2000 : ℚ) : ℝ)) t)
    (h0 : |u 150 - 2105111091 / 2000000000| ≤ 1 / 5000000)
    (h0' : |v 150 - 2331774279 / 1250000000| ≤ 1 / 5000000) :
    (∀ t ∈ Icc (150 : ℝ) (14671 / 20), 0 < 2 * u t - v t) ∧
    (∀ t ∈ Icc (14671 / 20 : ℝ) (73399 / 100),
      6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t < 0 ∧
      (1020324 / 1000000 : ℝ) ≤ u t ∧ u t ≤ 1020415 / 1000000) ∧
    (∀ t ∈ Icc (73399 / 100 : ℝ) 2000, 2 * u t - v t < 0) ∧
    |u 2000 - 9804962057 / 10000000000| ≤ 7 / 100000 ∧
    |v 2000 - 20327898293 / 10000000000| ≤ 7 / 100000 := by
  have hX : ((2000 : ℚ) : ℝ) = 2000 := by norm_num
  have hu' : ∀ t ∈ Icc (c0.t0 : ℝ) ((2000 : ℚ) : ℝ),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((150 : ℚ) : ℝ) ((2000 : ℚ) : ℝ)) t := by
    rw [hX, show c0.t0 = 150 from rfl]; push_cast; exact hu
  have hv' : ∀ t ∈ Icc (c0.t0 : ℝ) ((2000 : ℚ) : ℝ),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((150 : ℚ) : ℝ) ((2000 : ℚ) : ℝ)) t := by
    rw [hX, show c0.t0 = 150 from rfl]; push_cast; exact hv
  have a0 : |u (c0.t0 : ℝ) - ((c0.pu.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [show c0.t0 = 150 from rfl, show c0.pu.headD 0 = 2105111091 / 2000000000 from rfl,
      show c0.δ = 1 / 5000000 from rfl]; push_cast; exact h0
  have b0 : |v (c0.t0 : ℝ) - ((c0.pv.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [show c0.t0 = 150 from rfl, show c0.pv.headD 0 = 2331774279 / 1250000000 from rfl,
      show c0.δ = 1 / 5000000 from rfl]; push_cast; exact h0'
  have p0 : (c0.t0 : ℝ) ≤ (c0.t0 : ℝ) := le_rfl
  obtain ⟨o0, i0, a1, b1⟩ := seg_q _ _ _ inc0_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p0], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p0], ht.2⟩) a0 b0
  have p1 := p0.trans o0
  have g0 := i0
  obtain ⟨o1, i1, a2, b2⟩ := seg_q _ _ _ inc1_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p1], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p1], ht.2⟩) a1 b1
  have p2 := p1.trans o1
  have g1 := icc_glue g0 i1
  obtain ⟨o2, i2, a3, b3⟩ := seg_q _ _ _ inc2_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p2], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p2], ht.2⟩) a2 b2
  have p3 := p2.trans o2
  have g2 := icc_glue g1 i2
  obtain ⟨o3, i3, a4, b4⟩ := seg_q _ _ _ inc3_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p3], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p3], ht.2⟩) a3 b3
  have p4 := p3.trans o3
  have g3 := icc_glue g2 i3
  obtain ⟨o4, i4, a5, b5⟩ := seg_q _ _ _ inc4_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p4], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p4], ht.2⟩) a4 b4
  have p5 := p4.trans o4
  have g4 := icc_glue g3 i4
  obtain ⟨o5, i5, a6, b6⟩ := seg_q _ _ _ inc5_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, p5], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, p5], ht.2⟩) a5 b5
  have p6 := p5.trans o5
  have g5 := icc_glue g4 i5
  -- the bracket cell
  have hok := br_ok
  have hok1 : decide (CellProp 150 2000 c83) = true := by
    simp only [cellOK, Bool.and_eq_true] at hok; exact hok.1
  have hT : ((c83.t0 : ℚ) : ℝ) + ((c83.h : ℚ) : ℝ) ≤ ((2000 : ℚ) : ℝ) := by
    exact_mod_cast (show c83.t0 + c83.h ≤ 2000 by decide +kernel)
  have hub : ∀ t ∈ Icc (c83.t0 : ℝ) (c83.t0 + c83.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc ((150 : ℚ) : ℝ) ((2000 : ℚ) : ℝ)) t := fun t ht =>
    hu' t ⟨by linarith [ht.1, p6], by linarith [ht.2, hT]⟩
  have hvb : ∀ t ∈ Icc (c83.t0 : ℝ) (c83.t0 + c83.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc ((150 : ℚ) : ℝ) ((2000 : ℚ) : ℝ)) t := fun t ht =>
    hv' t ⟨by linarith [ht.1, p6], by linarith [ht.2, hT]⟩
  have hcq := cell_q c83 hok1 hub hvb a6 b6
  obtain ⟨-, hend1, hend2⟩ := cell_facts c83 hok hub hvb a6 b6
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true br_link
  have he : ((c83.t0 + c83.h : ℚ) : ℝ) = (c84.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hend1 hend2
  have kE' : |((qeval c83.pu c83.h : ℚ) : ℝ) - ((c84.pu.headD 0 : ℚ) : ℝ)| + c83.B ≤ c84.δ := by
    exact_mod_cast kE
  have kφ' : |((qeval c83.pv c83.h : ℚ) : ℝ) - ((c84.pv.headD 0 : ℚ) : ℝ)| + c83.B ≤ c84.δ := by
    exact_mod_cast kφ
  have ai := abs_link hend1 kE'
  have bi := abs_link hend2 kφ'
  have q0 : (c0.t0 : ℝ) ≤ c84.t0 := by rw [← he]; linarith [p6, (show (0 : ℝ) < c83.h by exact_mod_cast (show (0 : ℚ) < c83.h by decide +kernel))]
  have r0 := q0
  obtain ⟨n0, j0, ai1, bi1⟩ := seg_q _ _ _ dec0_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, r0], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, r0], ht.2⟩) ai bi
  have r1 := r0.trans n0
  have f0 := j0
  obtain ⟨n1, j1, ai2, bi2⟩ := seg_q _ _ _ dec1_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, r1], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, r1], ht.2⟩) ai1 bi1
  have r2 := r1.trans n1
  have f1 := icc_glue f0 j1
  obtain ⟨n2, j2, ai3, bi3⟩ := seg_q _ _ _ dec2_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, r2], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, r2], ht.2⟩) ai2 bi2
  have r3 := r2.trans n2
  have f2 := icc_glue f1 j2
  obtain ⟨jl, kU, kV⟩ := end_q _ _ dec3_ok
    (fun t ht => hu' t ⟨by linarith [ht.1, r3], ht.2⟩) (fun t ht => hv' t ⟨by linarith [ht.1, r3], ht.2⟩) ai3 bi3
  have fdec := icc_glue f2 jl
  have e0 : (c0.t0 : ℝ) = 150 := by rw [show c0.t0 = 150 from rfl]; norm_num
  have eA : (c83.t0 : ℝ) = 14671 / 20 := by rw [show c83.t0 = 14671 / 20 from rfl]; norm_num
  have eB : (c84.t0 : ℝ) = 73399 / 100 := by rw [show c84.t0 = 73399 / 100 from rfl]; norm_num
  have eh : (c83.t0 : ℝ) + c83.h = 73399 / 100 := by rw [he, eB]
  have bu := of_decide_eq_true br_u
  have bu1 : ((1020324 / 1000000 : ℚ) : ℝ) ≤ ((lo c83.pu c83.h - c83.B : ℚ) : ℝ) := by exact_mod_cast bu.1
  have bu2 : ((hi c83.pu c83.h + c83.B : ℚ) : ℝ) ≤ ((1020415 / 1000000 : ℚ) : ℝ) := by exact_mod_cast bu.2
  push_cast at bu1 bu2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; rw [e0] at g5; exact g5 t ⟨ht.1, by rw [eA]; exact ht.2⟩
  · intro t ht
    have ht' : t ∈ Icc (c83.t0 : ℝ) (c83.t0 + c83.h) := ⟨by rw [eA]; exact ht.1, by rw [eh]; exact ht.2⟩
    obtain ⟨c1, c2⟩ := hcq t ht'
    have l1 := lo_le c83.pu (h := c83.h) (σ := t - c83.t0) (by linarith [ht'.1]) (by linarith [ht'.2])
    have l2 := le_hi c83.pu (h := c83.h) (σ := t - c83.t0) (by linarith [ht'.1]) (by linarith [ht'.2])
    have c1' := abs_le.1 c1
    exact ⟨neg_G c83 hok1 br_G ht' c1 c2, by linarith [c1'.1], by linarith [c1'.2]⟩
  · intro t ht; rw [eB] at fdec; exact fdec t ⟨ht.1, by rw [hX] at fdec; exact ht.2⟩
  · push_cast at kU; norm_num at kU ⊢; exact kU
  · push_cast at kV; norm_num at kV ⊢; exact kV

end Checked.Math.BEH2Chain
