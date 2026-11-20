import Checked.Math.GLamBands
import Checked.Math.GLam3Chain

/-! Gelfand problem, `GelfandLam3`: the value of the branch parameter λ(s) = s² e^{w(s)} of the regular isothermal solution at its fourth turning point, for every sequence of turning points with the monotonicity pattern of `Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the route of `Checked.Math.GLamBands.bands`, continued by the certified homology cells of `GLam3Chain` from the end of `GLamChain` (v above two up to the bracket, u below one on the bracket, v below two at its end), the zero of v − two in the bracket by the intermediate value theorem, identified with the fourth given turning point by strict monotonicity of λ at two points, and λ = two times u at a zero of v − two. Promoted from `Work/Math/GelfandLam3.lean` (run 2026-11-20T1028Z). -/

namespace Checked.Math.GelfandLam3
open Set Checked.Math.GelfandExtremaMain Checked.Math.GLamCell Checked.Math.GLamBands

set_option maxHeartbeats 4000000 in
/-- For the regular solution w of the radial Gelfand (isothermal) equation w'' + (2/s) w' + e^w = 0 with
w(0) = 0, and any strictly increasing sequence ζ whose first term lies in [4.071496844, 4.071496845] and
along which λ(s) = s² e^{w(s)} increases on [0, ζ 0] and then alternately decreases and increases, the value
of λ at ζ 3 (the fourth turning point) lies in [1.9637, 1.9707]. -/
theorem lam3_band (w φ : ℝ → ℝ)
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
    1.9637 ≤ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ∧ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ≤ 1.9707 := by
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
  have b3 := u6 z3 z3mem
  have l3 : ζ 3 ^ 2 * Real.exp (w (ζ 3)) = 2 * Uf z3 := by
    rw [e3]; have : U w φ z3 = Uf z3 := rfl; rw [← this, k3]; unfold lam; ring
  rw [l3]
  norm_num
  refine ⟨by linarith [b3.2.1], by linarith [b3.2.2]⟩

end Checked.Math.GelfandLam3
