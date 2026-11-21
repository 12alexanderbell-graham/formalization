import Checked.Math.GLamBands
import Checked.Math.GLam3Chain
import Checked.Math.GSegData

/-! Gelfand problem, `GelfandLam4`: the value of the branch parameter λ(s) = s² e^{w(s)} of the regular isothermal solution at its fourth and fifth turning points, for every sequence of turning points with the monotonicity pattern of `Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the route of `Checked.Math.GelfandLam3.lam3_band` up to the identification of the fourth turning point; then the contracting homology cells of `GSegData` in log radius from the end box of `GLamChain`: v above two before the first bracket, u in a window below one on it, v below two up to the second bracket, u in a window above one on it, v above two after it; the zeros of v − two in the brackets by the intermediate value theorem, the first equal to the fourth turning point (v strictly decreasing on the bracket of `GLam3Chain`), the second identified with the fifth turning point by strict monotonicity of λ at two points, and λ = two times u at a zero of v − two. Promoted from `Work/Math/GelfandLam4.lean` (run 2026-11-21T0428Z). -/

namespace Checked.Math.GelfandLam4
open Set Checked.Math.GelfandExtremaMain Checked.Math.GLamCell Checked.Math.GLamBands
open Checked.Math.GContract Checked.Math.GSeg Checked.Math.GSegData Checked.Sim

/-- A segment's facts in log radius moved to the radius. -/
theorem to_radius' {A B : ℝ} {Uf Vf : ℝ → ℝ} {R : ℝ → ℝ → Prop}
    (h : ∀ t ∈ Icc A B, R (Uf (Real.exp t)) (Vf (Real.exp t))) :
    ∀ s ∈ Icc (Real.exp A) (Real.exp B), R (Uf s) (Vf s) := by
  intro s hs
  have hpos : 0 < s := (Real.exp_pos _).trans_le hs.1
  have e : Real.exp (Real.log s) = s := Real.exp_log hpos
  have h1 : A ≤ Real.log s := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hs.1
  have h2 : Real.log s ≤ B := by
    rw [← Real.log_exp B]; exact Real.log_le_log hpos hs.2
  have := h (Real.log s) ⟨h1, h2⟩
  rwa [e] at this

/-- The radius 8579/20 times e^{5893/2500} (start of the first bracket) is at least 4380. -/
theorem s3a_ge : (4380 : ℝ) ≤ 8579 / 20 * Real.exp (5893 / 2500) := by
  have := exp_ge_sum (x := (5893 / 2500 : ℝ)) (by norm_num) 16
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

/-- The radius 8579/20 times e^{1179/500} (end of the first bracket) is at most 4700. -/
theorem s3b_le : 8579 / 20 * Real.exp (1179 / 500) ≤ (4700 : ℝ) := by
  have := exp_le_pow4 (x := (1179 / 500 : ℝ)) (by norm_num) (by norm_num) 10 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

set_option maxHeartbeats 8000000 in
/-- For the regular solution w of the radial Gelfand (isothermal) equation w'' + (2/s) w' + e^w = 0 with
w(0) = 0, and any strictly increasing sequence ζ whose first term lies in [4.071496844, 4.071496845] and
along which λ(s) = s² e^{w(s)} increases on [0, ζ 0] and then alternately decreases and increases, the value
of λ at ζ 3 lies in [1.967422, 1.967510] and the value of λ at ζ 4 lies in [2.009926, 2.010028]. -/
theorem lam34_band (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) (ζ : ℕ → ℝ) (hm : StrictMono ζ)
    (hz0lo : 4.071496844 ≤ ζ 0) (hz0hi : ζ 0 ≤ 4.071496845)
    (hinc0 : StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)))
    (hanti : ∀ k : ℕ,
      StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1))))
    (hmono : ∀ k : ℕ,
      StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) :
    (1.967422 ≤ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ∧ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ≤ 1.967510) ∧
    (2.009926 ≤ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ∧ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ≤ 2.010028) := by
  have E := hyp_of hw hφ0 hφ
  have hsub : Icc (0 : ℝ) (41 / 10) ⊆ Ici 0 := fun t ht => ht.1
  obtain ⟨-, hdec, hEA, hφA, hφB⟩ := Checked.Math.GCerts.chain (w := w) (φ := φ)
    (fun s hs => (hw s hs.1).mono hsub) (hφ0.mono hsub)
    (fun s hs => (hφ s hs.1).mono hsub) h0
  rw [abs_le] at hEA hφA hφB
  -- the homology variables
  set Uf : ℝ → ℝ := fun x => x * Real.exp (w x) / -φ x with hUf
  set Vf : ℝ → ℝ := fun x => -(x * φ x) with hVf
  have hu3 : ∀ t ∈ Icc (8579 / 20 : ℝ) (4700 : ℝ),
      HasDerivWithinAt Uf (Uf t * (3 - Uf t - Vf t) / t)
        (Icc ((8579/20 : ℚ) : ℝ) ((4700 : ℚ) : ℝ)) t := fun t ht =>
    (hom_at E (by linarith [ht.1])).1.hasDerivWithinAt
  have hv3 : ∀ t ∈ Icc (8579 / 20 : ℝ) (4700 : ℝ),
      HasDerivWithinAt Vf (Vf t * (Uf t - 1) / t)
        (Icc ((8579/20 : ℚ) : ℝ) ((4700 : ℚ) : ℝ)) t := fun t ht =>
    (hom_at E (by linarith [ht.1])).2.hasDerivWithinAt
  have hu : ∀ t ∈ Icc (1017874211 / 250000000 : ℝ) (8579 / 20 : ℝ),
      HasDerivWithinAt Uf (Uf t * (3 - Uf t - Vf t) / t)
        (Icc ((1017874211/250000000 : ℚ) : ℝ) ((8579/20 : ℚ) : ℝ)) t := fun t ht =>
    (hom_at E (by linarith [ht.1])).1.hasDerivWithinAt
  have hv : ∀ t ∈ Icc (1017874211 / 250000000 : ℝ) (8579 / 20 : ℝ),
      HasDerivWithinAt Vf (Vf t * (Uf t - 1) / t)
        (Icc ((1017874211/250000000 : ℚ) : ℝ) ((8579/20 : ℚ) : ℝ)) t := fun t ht =>
    (hom_at E (by linarith [ht.1])).2.hasDerivWithinAt
  -- the start box at A
  have hA0 : (0 : ℝ) < 1017874211 / 250000000 := by norm_num
  have hP : 0 < -φ (1017874211 / 250000000) := by linarith [hφA.2]
  have hU0 : |Uf (1017874211 / 250000000) - 33219921185006153801 / 20000000000000000000| ≤
      4568267 / 125000000000000000 := by
    simp only [hUf]
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hP]
      nlinarith [hEA.1, hφA.2]
    · rw [sub_le_iff_le_add, div_le_iff₀ hP]
      nlinarith [hEA.2, hφA.1]
  have hV0 : |Vf (1017874211 / 250000000) - 49999999997579895251 / 25000000000000000000| ≤
      4568267 / 125000000000000000 := by
    simp only [hVf]
    rw [abs_le]
    constructor <;> nlinarith [hφA.1, hφA.2]
  obtain ⟨f1, f4, f2, f3, eU, eV⟩ := Checked.Math.GLamChain.chain hu hv hU0 hV0
  obtain ⟨g1, g4, -, eV3⟩ := Checked.Math.GLam3Chain.chain hu3 hv3 eU eV
  -- readable forms of the chain facts
  have v1 : ∀ t ∈ Icc (814299369 / 200000000 : ℝ) (37526789 / 1000000), 2 < Vf t :=
    fun t ht => (f1 t ht).1
  have u4 : ∀ t ∈ Icc (37526789 / 1000000 : ℝ) (37526809 / 1000000),
      Uf t < 1 ∧ (832077957837 / 1000000000000 : ℝ) ≤ Uf t ∧ Uf t ≤ 166415631879 / 200000000000 := by
    intro t ht
    obtain ⟨a, b, c⟩ := f4 t ht
    push_cast at b c
    exact ⟨a, b, c⟩
  have v2 : ∀ t ∈ Icc (37526809 / 1000000 : ℝ) (10722 / 25), Vf t < 2 :=
    fun t ht => (f2 t ht).1
  have u3 : ∀ t ∈ Icc (10722 / 25 : ℝ) (8579 / 20),
      1 < Uf t ∧ (1054260361137 / 1000000000000 : ℝ) ≤ Uf t ∧ Uf t ≤ 1054289419599 / 1000000000000 := by
    intro t ht
    obtain ⟨a, b, c⟩ := f3 t ht
    push_cast at b c
    exact ⟨a, b, c⟩
  have vQ2 : 2 < Vf (8579 / 20) := by
    have := (abs_le.1 eV).1
    linarith
  -- Y = v − 2
  have hYV : ∀ x, Y φ x = Vf x - 2 := fun x => rfl
  -- the first turning point: Y strictly increasing on [3, B0]
  have Ymono : StrictMonoOn (Y φ) (Icc 3 (814299369 / 200000000)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((Y_cont E).mono fun t ht => le_trans (by norm_num) ht.1)
    intro x hx
    rw [interior_Icc] at hx
    rw [(Y_deriv E (by linarith [hx.1])).deriv]
    exact hdec x (Ioo_subset_Icc_self hx)
  have YA : Y φ (1017874211 / 250000000) < 0 := by
    rw [hYV]; simp only [hVf]; nlinarith [hφA.1]
  have YB : 0 < Y φ (814299369 / 200000000) := by
    rw [hYV]; simp only [hVf]; nlinarith [hφB.2]
  obtain ⟨z0, hz0, hYz0⟩ : ∃ z0 ∈ Ioo (1017874211 / 250000000 : ℝ) (814299369 / 200000000), Y φ z0 = 0 :=
    intermediate_value_Ioo (by norm_num)
      ((Y_cont E).mono fun t ht => le_trans (by norm_num) ht.1) ⟨YA, YB⟩
  have z0mem : z0 ∈ Icc (3 : ℝ) (814299369 / 200000000) := ⟨by linarith [hz0.1], hz0.2.le⟩
  -- the second turning point: v strictly decreasing on [P1, Q1]
  have Vanti := V_anti E (a := 37526789 / 1000000) (b := 37526809 / 1000000) (by norm_num)
    fun x hx => (u4 x hx).1
  have VP1 : 2 < Vf (37526789 / 1000000) := v1 _ ⟨by norm_num, le_rfl⟩
  have VQ1 : Vf (37526809 / 1000000) < 2 := v2 _ ⟨le_rfl, by norm_num⟩
  obtain ⟨z1, hz1, hVz1⟩ : ∃ z1 ∈ Ioo (37526789 / 1000000 : ℝ) (37526809 / 1000000), Vf z1 = 2 :=
    intermediate_value_Ioo' (by norm_num)
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨VQ1, VP1⟩
  have z1mem : z1 ∈ Icc (37526789 / 1000000 : ℝ) (37526809 / 1000000) := Ioo_subset_Icc_self hz1
  -- the third turning point: v strictly increasing on [P2, Q2]
  have Vmono := V_mono E (a := 10722 / 25) (b := 8579 / 20) (by norm_num) fun x hx => (u3 x hx).1
  have VP2 : Vf (10722 / 25) < 2 := v2 _ ⟨by norm_num, le_rfl⟩
  obtain ⟨z2, hz2, hVz2⟩ : ∃ z2 ∈ Ioo (10722 / 25 : ℝ) (8579 / 20), Vf z2 = 2 :=
    intermediate_value_Ioo (by norm_num)
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨VP2, vQ2⟩
  have z2mem : z2 ∈ Icc (10722 / 25 : ℝ) (8579 / 20) := Ioo_subset_Icc_self hz2
  -- signs of Y between the zeros
  have Y0 : ∀ x ∈ Ioo (3 : ℝ) z0, Y φ x < 0 := fun x hx => by
    rw [← hYz0]; exact Ymono ⟨hx.1.le, by linarith [hx.2, z0mem.2]⟩ z0mem hx.2
  have Y01 : ∀ x ∈ Ioo z0 z1, 0 < Y φ x := by
    intro x hx
    rcases le_or_gt x (814299369 / 200000000) with h | h
    · rw [← hYz0]; exact Ymono z0mem ⟨by linarith [hx.1, z0mem.1], h⟩ hx.1
    rcases le_or_gt x (37526789 / 1000000) with h' | h'
    · rw [hYV]; linarith [v1 x ⟨h.le, h'⟩]
    · rw [hYV]
      have := Vanti ⟨h'.le, by linarith [hx.2, z1mem.2]⟩ z1mem hx.2
      linarith
  have Y12 : ∀ x ∈ Ioo z1 z2, Y φ x < 0 := by
    intro x hx
    rcases le_or_gt x (37526809 / 1000000) with h | h
    · rw [hYV]
      have := Vanti z1mem ⟨by linarith [hx.1, z1mem.1], h⟩ hx.1
      linarith
    rcases le_or_gt x (10722 / 25) with h' | h'
    · rw [hYV]; linarith [v2 x ⟨h.le, h'⟩]
    · rw [hYV]
      have := Vmono ⟨h'.le, by linarith [hx.2, z2mem.2]⟩ z2mem hx.2
      linarith
  have Y2 : ∀ x ∈ Ioo z2 (8579 / 20), 0 < Y φ x := by
    intro x hx
    rw [hYV]
    have := Vmono z2mem ⟨by linarith [hx.1, z2mem.1], hx.2.le⟩ hx.1
    linarith
  have M0 := lam_mono E (a := 3) (b := z0) (by norm_num) Y0
  have A01 := lam_anti E (a := z0) (b := z1) (by linarith [z0mem.1]) Y01
  have M12 := lam_mono E (a := z1) (b := z2) (by linarith [z1mem.1]) Y12
  have A2 := lam_anti E (a := z2) (b := 8579 / 20) (by linarith [z2mem.1]) Y2
  -- the given turning points in lam form
  have I0 : StrictMonoOn (lam w) (Icc 0 (ζ 0)) := hinc0
  have D0 : StrictAntiOn (lam w) (Icc (ζ 0) (ζ 1)) := hanti 0
  have I1 : StrictMonoOn (lam w) (Icc (ζ 1) (ζ 2)) := hmono 0
  have D1 : StrictAntiOn (lam w) (Icc (ζ 2) (ζ 3)) := hanti 1
  have h01 : ζ 0 < ζ 1 := hm (by norm_num)
  have h12 : ζ 1 < ζ 2 := hm (by norm_num)
  have h23 : ζ 2 < ζ 3 := hm (by norm_num)
  norm_num at hz0lo hz0hi
  -- identification
  have e0 : ζ 0 = z0 := by
    rcases lt_trichotomy (ζ 0) z0 with h | h | h
    · exfalso
      exact no_both (a := ζ 0) (b := min z0 (ζ 1)) (lt_min h h01) M0 D0
        ⟨by linarith, h.le⟩ ⟨by linarith [le_min h.le h01.le], min_le_left _ _⟩
        ⟨le_rfl, h01.le⟩ ⟨le_min h.le h01.le, min_le_right _ _⟩
    · exact h
    · exfalso
      have hz1 : ζ 0 ≤ z1 := by linarith [z1mem.1, z0mem.2]
      exact no_both (a := z0) (b := ζ 0) h I0 A01 ⟨by linarith [z0mem.1], h.le⟩ ⟨by linarith, le_rfl⟩
        ⟨le_rfl, by linarith [z1mem.1, z0mem.2]⟩ ⟨h.le, hz1⟩
  have e1 : ζ 1 = z1 := by
    rcases lt_trichotomy (ζ 1) z1 with h | h | h
    · exfalso
      exact no_both (a := ζ 1) (b := min z1 (ζ 2)) (lt_min h h12) I1 A01
        ⟨le_rfl, h12.le⟩ ⟨le_min h.le h12.le, min_le_right _ _⟩
        ⟨by linarith, h.le⟩ ⟨by linarith [le_min h.le h12.le], min_le_left _ _⟩
    · exact h
    · exfalso
      have hlt : z1 < z2 := by linarith [z1mem.2, z2mem.1]
      exact no_both (a := z1) (b := min (ζ 1) z2) (lt_min h hlt) M12 D0
        ⟨le_rfl, hlt.le⟩ ⟨le_min h.le hlt.le, min_le_right _ _⟩
        ⟨by linarith [z0mem.2, z1mem.1], h.le⟩
        ⟨by linarith [le_min h.le hlt.le, z0mem.2, z1mem.1], min_le_left _ _⟩
  have e2 : ζ 2 = z2 := by
    rcases lt_trichotomy (ζ 2) z2 with h | h | h
    · exfalso
      exact no_both (a := ζ 2) (b := min z2 (ζ 3)) (lt_min h h23) M12 D1
        ⟨by linarith, h.le⟩ ⟨by linarith [le_min h.le h23.le], min_le_left _ _⟩
        ⟨le_rfl, h23.le⟩ ⟨le_min h.le h23.le, min_le_right _ _⟩
    · exact h
    · exfalso
      have hlt : z2 < 8579 / 20 := hz2.2
      exact no_both (a := z2) (b := min (ζ 2) (8579 / 20)) (lt_min h hlt) I1 A2
        ⟨by linarith [z1mem.2, z2mem.1], h.le⟩
        ⟨by linarith [le_min h.le hlt.le, z1mem.2, z2mem.1], min_le_left _ _⟩
        ⟨le_rfl, hlt.le⟩ ⟨le_min h.le hlt.le, min_le_right _ _⟩
  -- beyond the end of GLamChain: v > 2 on [8579/20, 4380], u < 1 on the bracket [4380, 4700], v(4700) < 2
  have v5 : ∀ t ∈ Icc (8579 / 20 : ℝ) 4380, 2 < Vf t := fun t ht => (g1 t ht).1
  have u6 : ∀ t ∈ Icc (4380 : ℝ) 4700,
      Uf t < 1 ∧ (7670784487 / 7812500000 : ℝ) ≤ Uf t ∧ Uf t ≤ 985318556511 / 1000000000000 := by
    intro t ht
    obtain ⟨a, b, c⟩ := g4 t ht
    push_cast at b c
    exact ⟨a, b, c⟩
  have vQ3 : Vf 4700 < 2 := by
    have := (abs_le.1 eV3).2
    linarith
  have Vanti3 := V_anti E (a := 4380) (b := 4700) (by norm_num) fun x hx => (u6 x hx).1
  have VP3 : 2 < Vf 4380 := v5 _ ⟨by norm_num, le_rfl⟩
  obtain ⟨z3, hz3, hVz3⟩ : ∃ z3 ∈ Ioo (4380 : ℝ) 4700, Vf z3 = 2 :=
    intermediate_value_Ioo' (by norm_num)
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨vQ3, VP3⟩
  have z3mem : z3 ∈ Icc (4380 : ℝ) 4700 := Ioo_subset_Icc_self hz3
  have Y23 : ∀ x ∈ Ioo z2 z3, 0 < Y φ x := by
    intro x hx
    rcases lt_or_ge x (8579 / 20) with h | h
    · exact Y2 x ⟨hx.1, h⟩
    rcases le_or_gt x 4380 with h' | h'
    · rw [hYV]; linarith [v5 x ⟨h, h'⟩]
    · rw [hYV]
      have := Vanti3 ⟨h'.le, by linarith [hx.2, z3mem.2]⟩ z3mem hx.2
      linarith
  have Y3 : ∀ x ∈ Ioo z3 4700, Y φ x < 0 := by
    intro x hx
    rw [hYV]
    have := Vanti3 z3mem ⟨by linarith [hx.1, z3mem.1], hx.2.le⟩ hx.1
    linarith
  have A23 := lam_anti E (a := z2) (b := z3) (by linarith [z2mem.1]) Y23
  have M3 := lam_mono E (a := z3) (b := 4700) (by linarith [z3mem.1]) Y3
  have I2 : StrictMonoOn (lam w) (Icc (ζ 3) (ζ 4)) := hmono 1
  have h34 : ζ 3 < ζ 4 := hm (by norm_num)
  have e3 : ζ 3 = z3 := by
    rcases lt_trichotomy (ζ 3) z3 with h | h | h
    · exfalso
      exact no_both (a := ζ 3) (b := min z3 (ζ 4)) (lt_min h h34) I2 A23
        ⟨le_rfl, h34.le⟩ ⟨le_min h.le h34.le, min_le_right _ _⟩
        ⟨by rw [← e2]; exact h23.le, h.le⟩ ⟨by rw [← e2]; linarith [le_min h.le h34.le, h23], min_le_left _ _⟩
    · exact h
    · exfalso
      have hlt : z3 < 4700 := hz3.2
      exact no_both (a := z3) (b := min (ζ 3) 4700) (lt_min h hlt) M3 D1
        ⟨le_rfl, hlt.le⟩ ⟨le_min h.le hlt.le, min_le_right _ _⟩
        ⟨by rw [e2]; linarith [z2mem.2, z3mem.1], h.le⟩
        ⟨by rw [e2]; linarith [le_min h.le hlt.le, z2mem.2, z3mem.1], min_le_left _ _⟩
  have z3pos : 0 < z3 := by linarith [z3mem.1]
  have k3 := at_zero_U E z3pos (by rw [hYV, hVz3]; ring)
  have l3 : ζ 3 ^ 2 * Real.exp (w (ζ 3)) = 2 * Uf z3 := by
    rw [e3]; have : U w φ z3 = Uf z3 := rfl; rw [← this, k3]; unfold lam; ring
  -- the contracting cells in log radius
  set τ₀ : ℝ := Real.log (8579 / 20) with hτ₀
  have hdr : ∀ τ : ℝ, HasDerivAt (fun x => Uf (Real.exp x)) (F1 (Uf (Real.exp τ)) (Vf (Real.exp τ))) τ ∧
      HasDerivAt (fun x => Vf (Real.exp x)) (F2 (Uf (Real.exp τ)) (Vf (Real.exp τ))) τ := fun τ =>
    log_radius (hom_at E (Real.exp_pos τ)).1 (hom_at E (Real.exp_pos τ)).2
  have du : ∀ (a b : ℝ), ∀ t ∈ Icc a b, HasDerivWithinAt (fun x => Uf (Real.exp x))
      (F1 (Uf (Real.exp t)) (Vf (Real.exp t))) (Icc a b) t := fun a b t _ => (hdr t).1.hasDerivWithinAt
  have dv : ∀ (a b : ℝ), ∀ t ∈ Icc a b, HasDerivWithinAt (fun x => Vf (Real.exp x))
      (F2 (Uf (Real.exp t)) (Vf (Real.exp t))) (Icc a b) t := fun a b t _ => (hdr t).2.hasDerivWithinAt
  have hexp0 : Real.exp τ₀ = 8579 / 20 := by rw [hτ₀, Real.exp_log (by norm_num)]
  -- start of the first segment: the end box of GLamChain
  have st : Q (Uf (Real.exp τ₀) - evalQ (hd segA).pu 0) (Vf (Real.exp τ₀) - evalQ (hd segA).pv 0) ≤
      (hd segA).δ := by
    obtain ⟨s1, s2, s3⟩ := start_ok
    show Q (Uf (Real.exp τ₀) - evalQ a0.pu 0) (Vf (Real.exp τ₀) - evalQ a0.pv 0) ≤ a0.δ
    rw [evalQ_headD, evalQ_headD, s1, s2, hexp0]
    have s3' : ((7 / 2 * (649 / 125000000) ^ 2 : ℚ) : ℝ) ≤ (a0.δ : ℝ) := by exact_mod_cast s3
    push_cast at s3' ⊢
    have a1 := abs_le.1 eU; have a2 := abs_le.1 eV
    unfold Q
    nlinarith [mul_self_nonneg (Uf (8579/20) - 131783194069 / 125000000000 + (Vf (8579/20) - 1000004740803 / 500000000000)),
      mul_self_nonneg (Uf (8579/20) - 131783194069 / 125000000000 - (Vf (8579/20) - 1000004740803 / 500000000000))]
  have neA : segA ≠ [] := by unfold segA; exact List.cons_ne_nil _ _
  have neP : segP ≠ [] := by unfold segP; exact List.cons_ne_nil _ _
  have neC3 : segC3 ≠ [] := by unfold segC3; exact List.cons_ne_nil _ _
  have neB : segB ≠ [] := by unfold segB; exact List.cons_ne_nil _ _
  have neC4 : segC4 ≠ [] := by unfold segC4; exact List.cons_ne_nil _ _
  have neD : segD ≠ [] := by unfold segD; exact List.cons_ne_nil _ _
  -- segment A
  have endA := chain_end segA _ segA_len segA_ok neA (τ₀ := τ₀) (du _ _) (dv _ _) st
  have stP := link_q (c := lst segA) (d := hd segP) linkAP endA
  -- segment P: v above two
  set tP : ℝ := τ₀ + ((1467 / 625 : ℚ) : ℝ) with htP
  have allP := seg_all' (fun _ b => ((2 : ℚ) : ℝ) < b) (vGtB 2) (vGt_rel 2) segP _ segP_len segP_ok neP
    segP_pred (τ₀ := tP) (du _ _) (dv _ _) stP
  have endP := chain_end segP _ segP_len segP_ok neP (τ₀ := tP) (du _ _) (dv _ _) stP
  have stC3 := link_q (c := lst segP) (d := hd segC3) linkPC3 endP
  -- segment C3: u in [L3, U3]
  set tC3 : ℝ := tP + ((1 / 100 : ℚ) : ℝ) with htC3
  have allC3 := seg_all' (fun a _ => ((L3 : ℚ) : ℝ) < a ∧ a < ((U3 : ℚ) : ℝ)) (uInB L3 U3) (uIn_rel L3 U3)
    segC3 _ segC3_len segC3_ok neC3 segC3_pred (τ₀ := tC3) (du _ _) (dv _ _) stC3
  have endC3 := chain_end segC3 _ segC3_len segC3_ok neC3 (τ₀ := tC3) (du _ _) (dv _ _) stC3
  have stB := link_q (c := lst segC3) (d := hd segB) linkC3B endC3
  -- segment B: v below two
  set tB : ℝ := tC3 + ((1 / 1250 : ℚ) : ℝ) with htB
  have allB := seg_all' (fun _ b => b < ((2 : ℚ) : ℝ)) (vLtB 2) (vLt_rel 2) segB _ segB_len segB_ok neB
    segB_pred (τ₀ := tB) (du _ _) (dv _ _) stB
  have endB := chain_end segB _ segB_len segB_ok neB (τ₀ := tB) (du _ _) (dv _ _) stB
  have stC4 := link_q (c := lst segB) (d := hd segC4) linkBC4 endB
  -- segment C4: u in [L4, U4]
  set tC4 : ℝ := tB + ((11889 / 5000 : ℚ) : ℝ) with htC4
  have allC4 := seg_all' (fun a _ => ((L4 : ℚ) : ℝ) < a ∧ a < ((U4 : ℚ) : ℝ)) (uInB L4 U4) (uIn_rel L4 U4)
    segC4 _ segC4_len segC4_ok neC4 segC4_pred (τ₀ := tC4) (du _ _) (dv _ _) stC4
  have endC4 := chain_end segC4 _ segC4_len segC4_ok neC4 (τ₀ := tC4) (du _ _) (dv _ _) stC4
  have stD := link_q (c := lst segC4) (d := hd segD) linkC4D endC4
  -- segment D: v above two
  set tD : ℝ := tC4 + ((1 / 250 : ℚ) : ℝ) with htD
  have allD := seg_all' (fun _ b => ((2 : ℚ) : ℝ) < b) (vGtB 2) (vGt_rel 2) segD _ segD_len segD_ok neD
    segD_pred (τ₀ := tD) (du _ _) (dv _ _) stD
  -- in the radius
  have vP := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => ((2 : ℚ) : ℝ) < b) allP
  have uC3 := to_radius' (Uf := Uf) (Vf := Vf) (R := fun a _ => ((L3 : ℚ) : ℝ) < a ∧ a < ((U3 : ℚ) : ℝ)) allC3
  have vB := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => b < ((2 : ℚ) : ℝ)) allB
  have uC4 := to_radius' (Uf := Uf) (Vf := Vf) (R := fun a _ => ((L4 : ℚ) : ℝ) < a ∧ a < ((U4 : ℚ) : ℝ)) allC4
  have vD := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => ((2 : ℚ) : ℝ) < b) allD
  have eL3 : ((L3 : ℚ) : ℝ) = 983711 / 1000000 := by rw [show L3 = 983711 / 1000000 from rfl]; norm_num
  have eU3 : ((U3 : ℚ) : ℝ) = 196751 / 200000 := by rw [show U3 = 196751 / 200000 from rfl]; norm_num
  have eL4 : ((L4 : ℚ) : ℝ) = 1004963 / 1000000 := by rw [show L4 = 1004963 / 1000000 from rfl]; norm_num
  have eU4 : ((U4 : ℚ) : ℝ) = 502507 / 500000 := by rw [show U4 = 502507 / 500000 from rfl]; norm_num
  have e2 : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [eL3, eU3] at uC3; rw [eL4, eU4] at uC4; rw [e2] at vP vB vD
  have qC3 : tC3 = τ₀ + 5893 / 2500 := by rw [htC3, htP]; push_cast; ring
  have qB : tB = τ₀ + 1179 / 500 := by rw [htB, qC3]; push_cast; ring
  have qC4 : tC4 = τ₀ + 23679 / 5000 := by rw [htC4, qB]; push_cast; ring
  have qD : tD = τ₀ + 23699 / 5000 := by rw [htD, qC4]; push_cast; ring
  have qC3e : tC3 + ((1 / 1250 : ℚ) : ℝ) = tB := rfl
  have qBe : tB + ((11889 / 5000 : ℚ) : ℝ) = tC4 := rfl
  have qC4e : tC4 + ((1 / 250 : ℚ) : ℝ) = tD := rfl
  have qPe : tP + ((1 / 100 : ℚ) : ℝ) = tC3 := rfl
  set S3a : ℝ := Real.exp tC3 with hS3a
  set S3b : ℝ := Real.exp tB with hS3b
  set S4a : ℝ := Real.exp tC4 with hS4a
  set S4b : ℝ := Real.exp tD with hS4b
  have eS3a : S3a = 8579 / 20 * Real.exp (5893 / 2500) := by rw [hS3a, qC3, Real.exp_add, hexp0]
  have eS3b : S3b = 8579 / 20 * Real.exp (1179 / 500) := by rw [hS3b, qB, Real.exp_add, hexp0]
  have p3a : 4380 ≤ S3a := by rw [eS3a]; exact s3a_ge
  have p3b : S3b ≤ 4700 := by rw [eS3b]; exact s3b_le
  have o3 : S3a < S3b := by rw [hS3a, hS3b, qC3, qB]; apply Real.exp_lt_exp.2; linarith
  have o34 : S3b < S4a := by rw [hS3b, hS4a, qB, qC4]; apply Real.exp_lt_exp.2; linarith
  have o4 : S4a < S4b := by rw [hS4a, hS4b, qC4, qD]; apply Real.exp_lt_exp.2; linarith
  have oP : Real.exp tP ≤ S3a := by rw [hS3a, ← qPe]; apply Real.exp_le_exp.2; push_cast; linarith
  have oE : S4b ≤ Real.exp (tD + ((1 / 1000 : ℚ) : ℝ)) := by rw [hS4b]; apply Real.exp_le_exp.2; push_cast; linarith
  -- the facts at the bracket ends
  have v3a : 2 < Vf S3a := vP S3a ⟨oP, le_rfl⟩
  have v3b : Vf S3b < 2 := vB S3b ⟨le_rfl, o34.le⟩
  have v4a : Vf S4a < 2 := vB S4a ⟨o34.le, le_rfl⟩
  have v4b : 2 < Vf S4b := vD S4b ⟨le_rfl, oE⟩
  have s3apos : 0 < S3a := Real.exp_pos _
  have s4apos : 0 < S4a := Real.exp_pos _
  -- the fourth turning point is in the first bracket
  have Vanti3' := V_anti E (a := S3a) (b := S3b) s3apos fun x hx =>
    lt_trans (uC3 x hx).2 (by norm_num)
  obtain ⟨y3, hy3, hVy3⟩ : ∃ y3 ∈ Ioo S3a S3b, Vf y3 = 2 :=
    intermediate_value_Ioo' o3.le
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨v3b, v3a⟩
  have y3mem : y3 ∈ Icc (4380 : ℝ) 4700 := ⟨by linarith [hy3.1], by linarith [hy3.2]⟩
  have ez3 : z3 = y3 := Vanti3.injOn z3mem y3mem (by show Vf z3 = Vf y3; rw [hVz3, hVy3])
  have z3in : z3 ∈ Icc S3a S3b := by rw [ez3]; exact Ioo_subset_Icc_self hy3
  -- the fifth turning point is in the second bracket
  have Vmono4 := V_mono E (a := S4a) (b := S4b) s4apos fun x hx =>
    lt_trans (by norm_num) (uC4 x hx).1
  obtain ⟨z4, hz4, hVz4⟩ : ∃ z4 ∈ Ioo S4a S4b, Vf z4 = 2 :=
    intermediate_value_Ioo o4.le
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨v4a, v4b⟩
  have z4mem : z4 ∈ Icc S4a S4b := Ioo_subset_Icc_self hz4
  have Y34 : ∀ x ∈ Ioo z3 z4, Y φ x < 0 := by
    intro x hx
    rw [hYV]
    rcases le_or_gt x S3b with h | h
    · have := Vanti3' z3in ⟨by linarith [hx.1, z3in.1], h⟩ hx.1
      linarith
    rcases le_or_gt x S4a with h' | h'
    · linarith [vB x ⟨h.le, h'⟩]
    · have := Vmono4 ⟨h'.le, by linarith [hx.2, z4mem.2]⟩ z4mem hx.2
      linarith
  have Y4 : ∀ x ∈ Ioo z4 S4b, 0 < Y φ x := by
    intro x hx
    rw [hYV]
    have := Vmono4 z4mem ⟨by linarith [hx.1, z4mem.1], hx.2.le⟩ hx.1
    linarith
  have M34 := lam_mono E (a := z3) (b := z4) (by linarith [z3mem.1]) Y34
  have A4 := lam_anti E (a := z4) (b := S4b) (by linarith [z4mem.1]) Y4
  have I2 : StrictMonoOn (lam w) (Icc (ζ 3) (ζ 4)) := hmono 1
  have D2 : StrictAntiOn (lam w) (Icc (ζ 4) (ζ 5)) := hanti 2
  have h45 : ζ 4 < ζ 5 := hm (by norm_num)
  have z34 : z3 < z4 := by linarith [z3in.2, z4mem.1]
  have e4 : ζ 4 = z4 := by
    rcases lt_trichotomy (ζ 4) z4 with h | h | h
    · exfalso
      exact no_both (a := ζ 4) (b := min z4 (ζ 5)) (lt_min h h45) M34 D2
        ⟨by rw [← e3]; exact h34.le, h.le⟩ ⟨by rw [← e3]; linarith [le_min h.le h45.le, h34], min_le_left _ _⟩
        ⟨le_rfl, h45.le⟩ ⟨le_min h.le h45.le, min_le_right _ _⟩
    · exact h
    · exfalso
      have hlt : z4 < S4b := hz4.2
      exact no_both (a := z4) (b := min (ζ 4) S4b) (lt_min h hlt) I2 A4
        ⟨by rw [e3]; exact z34.le, h.le⟩ ⟨by rw [e3]; linarith [le_min h.le hlt.le], min_le_left _ _⟩
        ⟨le_rfl, hlt.le⟩ ⟨le_min h.le hlt.le, min_le_right _ _⟩
  have z3pos : 0 < z3 := by linarith [z3mem.1]
  have k3 := at_zero_U E z3pos (by rw [hYV, hVz3]; ring)
  have l3 : ζ 3 ^ 2 * Real.exp (w (ζ 3)) = 2 * Uf z3 := by
    rw [e3]; have : U w φ z3 = Uf z3 := rfl; rw [← this, k3]; unfold lam; ring
  have z4pos : 0 < z4 := by linarith [z4mem.1]
  have k4 := at_zero_U E z4pos (by rw [hYV, hVz4]; ring)
  have l4 : ζ 4 ^ 2 * Real.exp (w (ζ 4)) = 2 * Uf z4 := by
    rw [e4]; have : U w φ z4 = Uf z4 := rfl; rw [← this, k4]; unfold lam; ring
  have b3 := uC3 z3 z3in
  have b4 := uC4 z4 z4mem
  rw [l3, l4]
  norm_num
  exact ⟨⟨by linarith [b3.1], by linarith [b3.2]⟩, ⟨by linarith [b4.1], by linarith [b4.2]⟩⟩

end Checked.Math.GelfandLam4
