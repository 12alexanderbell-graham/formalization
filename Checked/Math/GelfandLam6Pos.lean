import Checked.Math.GelfandLam6

/-! Gelfand problem, `GelfandLam6Pos`: a lower bound on the radius of the seventh turning point of the radial branch, for every sequence of turning points with the monotonicity pattern of `Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the proof of `Checked.Math.GelfandLam6.lam3456_band` up to the identification of that turning point with the zero of v minus two in its bracket, whose left end is the exponential of a rational offset from the logarithm of the start radius (run 2026-11-25T1028Z). -/

namespace Checked.Math.GelfandLam6Pos
open Set Checked.Math.GelfandExtremaMain Checked.Math.GLamCell Checked.Math.GLamBands
open Checked.Math.GContract Checked.Math.GSeg Checked.Math.GSegData Checked.Math.GSegData7 Checked.Sim
open Checked.Math.GelfandLam4

set_option maxHeartbeats 16000000 in
/-- For the regular solution w of the radial Gelfand (isothermal) equation w'' + (2/s) w' + e^w = 0 with
w(0) = 0, and any strictly increasing sequence ζ whose first term lies in [4.071496844, 4.071496845] and
along which λ(s) = s² e^{w(s)} increases on [0, ζ 0] and then alternately decreases and increases, the
radius ζ 6 is at least three hundred thousand. -/
theorem zeta6_ge (w φ : ℝ → ℝ)
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
    300000 ≤ ζ 6 := by
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
  -- segment D to its end; the segments of GSegData7
  have endD := chain_end segD _ segD_len segD_ok neD (τ₀ := tD) (du _ _) (dv _ _) stD
  have stE := link_q (c := lst segD) (d := hd segE) linkDE endD
  have neE : segE ≠ [] := by unfold segE; exact List.cons_ne_nil _ _
  have neC5 : segC5 ≠ [] := by unfold segC5; exact List.cons_ne_nil _ _
  have neF : segF ≠ [] := by unfold segF; exact List.cons_ne_nil _ _
  have neC6 : segC6 ≠ [] := by unfold segC6; exact List.cons_ne_nil _ _
  have neG : segG ≠ [] := by unfold segG; exact List.cons_ne_nil _ _
  -- segment E: v above two
  set tE : ℝ := tD + ((1 / 1000 : ℚ) : ℝ) with htE
  have allE := seg_all' (fun _ b => ((2 : ℚ) : ℝ) < b) (vGtB 2) (vGt_rel 2) segE _ segE_len segE_ok neE
    segE_pred (τ₀ := tE) (du _ _) (dv _ _) stE
  have endE := chain_end segE _ segE_len segE_ok neE (τ₀ := tE) (du _ _) (dv _ _) stE
  have stC5 := link_q (c := lst segE) (d := hd segC5) linkEC5 endE
  -- segment C5: u in [L5, U5]
  set tC5 : ℝ := tE + ((11801 / 5000 : ℚ) : ℝ) with htC5
  have allC5 := seg_all' (fun a _ => ((L5 : ℚ) : ℝ) < a ∧ a < ((U5 : ℚ) : ℝ)) (uInB L5 U5) (uIn_rel L5 U5)
    segC5 _ segC5_len segC5_ok neC5 segC5_pred (τ₀ := tC5) (du _ _) (dv _ _) stC5
  have endC5 := chain_end segC5 _ segC5_len segC5_ok neC5 (τ₀ := tC5) (du _ _) (dv _ _) stC5
  have stF := link_q (c := lst segC5) (d := hd segF) linkC5F endC5
  -- segment F: v below two
  set tF : ℝ := tC5 + ((1 / 50 : ℚ) : ℝ) with htF
  have allF := seg_all' (fun _ b => b < ((2 : ℚ) : ℝ)) (vLtB 2) (vLt_rel 2) segF _ segF_len segF_ok neF
    segF_pred (τ₀ := tF) (du _ _) (dv _ _) stF
  have endF := chain_end segF _ segF_len segF_ok neF (τ₀ := tF) (du _ _) (dv _ _) stF
  have stC6 := link_q (c := lst segF) (d := hd segC6) linkFC6 endF
  -- segment C6: u in [L6, U6]
  set tC6 : ℝ := tF + ((23403 / 10000 : ℚ) : ℝ) with htC6
  have allC6 := seg_all' (fun a _ => ((L6 : ℚ) : ℝ) < a ∧ a < ((U6 : ℚ) : ℝ)) (uInB L6 U6) (uIn_rel L6 U6)
    segC6 _ segC6_len segC6_ok neC6 segC6_pred (τ₀ := tC6) (du _ _) (dv _ _) stC6
  have endC6 := chain_end segC6 _ segC6_len segC6_ok neC6 (τ₀ := tC6) (du _ _) (dv _ _) stC6
  have stG := link_q (c := lst segC6) (d := hd segG) linkC6G endC6
  -- segment G: v above two
  set tG : ℝ := tC6 + ((1 / 20 : ℚ) : ℝ) with htG
  have allG := seg_all' (fun _ b => ((2 : ℚ) : ℝ) < b) (vGtB 2) (vGt_rel 2) segG _ segG_len segG_ok neG
    segG_pred (τ₀ := tG) (du _ _) (dv _ _) stG
  -- in the radius
  have vE := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => ((2 : ℚ) : ℝ) < b) allE
  have uC5 := to_radius' (Uf := Uf) (Vf := Vf) (R := fun a _ => ((L5 : ℚ) : ℝ) < a ∧ a < ((U5 : ℚ) : ℝ)) allC5
  have vF := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => b < ((2 : ℚ) : ℝ)) allF
  have uC6 := to_radius' (Uf := Uf) (Vf := Vf) (R := fun a _ => ((L6 : ℚ) : ℝ) < a ∧ a < ((U6 : ℚ) : ℝ)) allC6
  have vG := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => ((2 : ℚ) : ℝ) < b) allG
  have eL5 : ((L5 : ℚ) : ℝ) = 9984509 / 10000000 := by rw [show L5 = 9984509 / 10000000 from rfl]; norm_num
  have eU5 : ((U5 : ℚ) : ℝ) = 9985113 / 10000000 := by rw [show U5 = 9985113 / 10000000 from rfl]; norm_num
  have eL6 : ((L6 : ℚ) : ℝ) = 625273 / 625000 := by rw [show L6 = 625273 / 625000 from rfl]; norm_num
  have eU6 : ((U6 : ℚ) : ℝ) = 100049 / 100000 := by rw [show U6 = 100049 / 100000 from rfl]; norm_num
  rw [eL5, eU5] at uC5; rw [eL6, eU6] at uC6; rw [e2] at vE vF vG
  set S5a : ℝ := Real.exp tC5 with hS5a
  set S5b : ℝ := Real.exp tF with hS5b
  set S6a : ℝ := Real.exp tC6 with hS6a
  set S6b : ℝ := Real.exp tG with hS6b
  have o5 : S5a < S5b := by rw [hS5a, hS5b, htF]; apply Real.exp_lt_exp.2; push_cast; linarith
  have o56 : S5b < S6a := by rw [hS5b, hS6a, htC6]; apply Real.exp_lt_exp.2; push_cast; linarith
  have o6 : S6a < S6b := by rw [hS6a, hS6b, htG]; apply Real.exp_lt_exp.2; push_cast; linarith
  have oDE : Real.exp (tD + ((1 / 1000 : ℚ) : ℝ)) = Real.exp tE := rfl
  have oE5 : Real.exp tE ≤ S5a := by rw [hS5a, htC5]; apply Real.exp_le_exp.2; push_cast; linarith
  have oG : S6b ≤ Real.exp (tG + ((1 / 1000 : ℚ) : ℝ)) := by
    rw [hS6b]; apply Real.exp_le_exp.2; push_cast; linarith
  have o45 : S4b ≤ Real.exp tE := by rw [hS4b, htE]; apply Real.exp_le_exp.2; push_cast; linarith
  -- the facts at the bracket ends
  have v5a : 2 < Vf S5a := vE S5a ⟨oE5, le_rfl⟩
  have v5b : Vf S5b < 2 := vF S5b ⟨le_rfl, o56.le⟩
  have v6a : Vf S6a < 2 := vF S6a ⟨o56.le, le_rfl⟩
  have v6b : 2 < Vf S6b := vG S6b ⟨le_rfl, oG⟩
  have s5apos : 0 < S5a := Real.exp_pos _
  have s6apos : 0 < S6a := Real.exp_pos _
  -- the sixth turning point is in the third bracket (u below one: v decreasing)
  have Vanti5 := V_anti E (a := S5a) (b := S5b) s5apos fun x hx =>
    lt_trans (uC5 x hx).2 (by norm_num)
  obtain ⟨z5, hz5, hVz5⟩ : ∃ z5 ∈ Ioo S5a S5b, Vf z5 = 2 :=
    intermediate_value_Ioo' o5.le
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨v5b, v5a⟩
  have z5mem : z5 ∈ Icc S5a S5b := Ioo_subset_Icc_self hz5
  -- the seventh turning point is in the fourth bracket (u above one: v increasing)
  have Vmono6 := V_mono E (a := S6a) (b := S6b) s6apos fun x hx =>
    lt_trans (by norm_num) (uC6 x hx).1
  obtain ⟨z6, hz6, hVz6⟩ : ∃ z6 ∈ Ioo S6a S6b, Vf z6 = 2 :=
    intermediate_value_Ioo o6.le
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨v6a, v6b⟩
  have z6mem : z6 ∈ Icc S6a S6b := Ioo_subset_Icc_self hz6
  have z45 : z4 < z5 := by linarith [hz4.2, z5mem.1, o45, oE5]
  have z56 : z5 < z6 := by linarith [hz5.2, z6mem.1, o56]
  -- signs of Y between the zeros
  have Y45 : ∀ x ∈ Ioo z4 z5, 0 < Y φ x := by
    intro x hx
    rw [hYV]
    rcases le_or_gt x S4b with h | h
    · have := Vmono4 z4mem ⟨by linarith [hx.1, z4mem.1], h⟩ hx.1
      linarith
    rcases le_or_gt x (Real.exp tE) with h' | h'
    · linarith [vD x ⟨h.le, h'⟩]
    rcases le_or_gt x S5a with h'' | h''
    · linarith [vE x ⟨h'.le, h''⟩]
    · have := Vanti5 ⟨h''.le, by linarith [hx.2, z5mem.2]⟩ z5mem hx.2
      linarith
  have Y56 : ∀ x ∈ Ioo z5 z6, Y φ x < 0 := by
    intro x hx
    rw [hYV]
    rcases le_or_gt x S5b with h | h
    · have := Vanti5 z5mem ⟨by linarith [hx.1, z5mem.1], h⟩ hx.1
      linarith
    rcases le_or_gt x S6a with h' | h'
    · linarith [vF x ⟨h.le, h'⟩]
    · have := Vmono6 ⟨h'.le, by linarith [hx.2, z6mem.2]⟩ z6mem hx.2
      linarith
  have Y6 : ∀ x ∈ Ioo z6 S6b, 0 < Y φ x := by
    intro x hx
    rw [hYV]
    have := Vmono6 z6mem ⟨by linarith [hx.1, z6mem.1], hx.2.le⟩ hx.1
    linarith
  have A45 := lam_anti E (a := z4) (b := z5) (by linarith [z4mem.1]) Y45
  have M56 := lam_mono E (a := z5) (b := z6) (by linarith [z5mem.1]) Y56
  have A6 := lam_anti E (a := z6) (b := S6b) (by linarith [z6mem.1]) Y6
  have I3 : StrictMonoOn (lam w) (Icc (ζ 5) (ζ 6)) := hmono 2
  have D3 : StrictAntiOn (lam w) (Icc (ζ 6) (ζ 7)) := hanti 3
  have h56 : ζ 5 < ζ 6 := hm (by norm_num)
  have h67 : ζ 6 < ζ 7 := hm (by norm_num)
  have e5 : ζ 5 = z5 := by
    rcases lt_trichotomy (ζ 5) z5 with h | h | h
    · exfalso
      exact no_both (a := ζ 5) (b := min z5 (ζ 6)) (lt_min h h56) I3 A45
        ⟨le_rfl, h56.le⟩ ⟨le_min h.le h56.le, min_le_right _ _⟩
        ⟨by rw [← e4]; exact h45.le, h.le⟩ ⟨by rw [← e4]; linarith [le_min h.le h56.le, h45], min_le_left _ _⟩
    · exact h
    · exfalso
      exact no_both (a := z5) (b := min (ζ 5) z6) (lt_min h z56) M56 D2
        ⟨le_rfl, z56.le⟩ ⟨le_min h.le z56.le, min_le_right _ _⟩
        ⟨by rw [e4]; exact z45.le, h.le⟩
        ⟨by rw [e4]; linarith [le_min h.le z56.le], min_le_left _ _⟩
  have e6 : ζ 6 = z6 := by
    rcases lt_trichotomy (ζ 6) z6 with h | h | h
    · exfalso
      exact no_both (a := ζ 6) (b := min z6 (ζ 7)) (lt_min h h67) M56 D3
        ⟨by rw [← e5]; exact h56.le, h.le⟩ ⟨by rw [← e5]; linarith [le_min h.le h67.le, h56], min_le_left _ _⟩
        ⟨le_rfl, h67.le⟩ ⟨le_min h.le h67.le, min_le_right _ _⟩
    · exact h
    · exfalso
      have hlt : z6 < S6b := hz6.2
      exact no_both (a := z6) (b := min (ζ 6) S6b) (lt_min h hlt) I3 A6
        ⟨by rw [e5]; exact z56.le, h.le⟩ ⟨by rw [e5]; linarith [le_min h.le hlt.le], min_le_left _ _⟩
        ⟨le_rfl, hlt.le⟩ ⟨le_min h.le hlt.le, min_le_right _ _⟩
  have qC6 : tC6 = τ₀ + 94613 / 10000 := by
    rw [htC6, htF, htC5, htE, htD, htC4, htB, htC3, htP]; push_cast; ring
  have hS6 : (300000 : ℝ) ≤ S6a := by
    rw [hS6a, qC6, Real.exp_add, hexp0]
    have := Real.pow_div_factorial_le_exp (x := (94613 / 10000 : ℝ)) (by norm_num) 7
    norm_num [Nat.factorial] at this ⊢
    nlinarith
  rw [e6]
  linarith [z6mem.1]

end Checked.Math.GelfandLam6Pos
