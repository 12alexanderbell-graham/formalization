import Checked.Math.GelfandExtremaMain
import Checked.Math.BEHMain
import Checked.Math.GChain
import Work.Math.GLamChain

/-! Gelfand problem, `GLamBands`: the values of the branch parameter λ(s) = s² e^{w(s)} of the regular isothermal
solution at its second and third turning points, for every sequence of turning points with the monotonicity
pattern of `Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the start enclosure of `Checked.Math.GCerts.chain`
at the first turning point, the certified homology cells of `GLamChain` beyond it (λ decreases where v exceeds two
and increases where v is below two; v is strictly monotone on the two bracket intervals), the zeros of v − 2 found
by the intermediate value theorem, identified with the given turning points by comparing strict monotonicity of λ
at two points, and λ = 2u at a zero of v − 2. -/

namespace Work.Math.GLamBands
open Set Checked.Math.GelfandExtremaMain Work.Math.GLamCell

/-- A function cannot be strictly increasing and strictly decreasing through the same two points. -/
theorem no_both {f : ℝ → ℝ} {S T : Set ℝ} {a b : ℝ} (hab : a < b) (hS : StrictMonoOn f S)
    (hT : StrictAntiOn f T) (haS : a ∈ S) (hbS : b ∈ S) (haT : a ∈ T) (hbT : b ∈ T) : False := by
  have h1 := hS haS hbS hab
  have h2 := hT haT hbT hab
  linarith

section
variable {w φ : ℝ → ℝ} (E : Hyp w φ)
include E

theorem lam_anti {a b : ℝ} (ha : 0 < a) (hY : ∀ x ∈ Ioo a b, 0 < Y φ x) :
    StrictAntiOn (lam w) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    ((lam_cont E).mono fun t ht => le_trans ha.le ht.1)
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := ha.trans hx.1
  rw [(lam_deriv E hx0).deriv]
  have := hY x hx
  have e : 2 + x * φ x = -Y φ x := by unfold Y; ring
  rw [e]
  exact mul_neg_of_pos_of_neg (mul_pos hx0 (Real.exp_pos _)) (by linarith)

theorem lam_mono {a b : ℝ} (ha : 0 < a) (hY : ∀ x ∈ Ioo a b, Y φ x < 0) :
    StrictMonoOn (lam w) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    ((lam_cont E).mono fun t ht => le_trans ha.le ht.1)
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := ha.trans hx.1
  rw [(lam_deriv E hx0).deriv]
  have := hY x hx
  have e : 2 + x * φ x = -Y φ x := by unfold Y; ring
  rw [e]
  exact mul_pos (mul_pos hx0 (Real.exp_pos _)) (by linarith)

/-- The homology variables and their derivatives at a positive radius. -/
theorem hom_at {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => x * Real.exp (w x) / -φ x)
      ((t * Real.exp (w t) / -φ t) * (3 - t * Real.exp (w t) / -φ t - -(t * φ t)) / t) t ∧
    HasDerivAt (fun x => -(x * φ x)) (-(t * φ t) * (t * Real.exp (w t) / -φ t - 1) / t) t :=
  Checked.Math.BEHMain.homology_deriv_at ht (phi_neg E ht) (E.dw t ht) (E.dφ t ht)

theorem V_anti {a b : ℝ} (ha : 0 < a) (hu : ∀ x ∈ Icc a b, x * Real.exp (w x) / -φ x < 1) :
    StrictAntiOn (fun x => -(x * φ x)) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun t ht => ((hom_at E (ha.trans_le ht.1)).2.continuousAt.continuousWithinAt))
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := ha.trans hx.1
  rw [(hom_at E hx0).2.deriv]
  have hv : 0 < -(x * φ x) := by have := phi_neg E hx0; nlinarith
  have := hu x (Ioo_subset_Icc_self hx)
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hv (by linarith)) hx0

theorem V_mono {a b : ℝ} (ha : 0 < a) (hu : ∀ x ∈ Icc a b, 1 < x * Real.exp (w x) / -φ x) :
    StrictMonoOn (fun x => -(x * φ x)) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun t ht => ((hom_at E (ha.trans_le ht.1)).2.continuousAt.continuousWithinAt))
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := ha.trans hx.1
  rw [(hom_at E hx0).2.deriv]
  have hv : 0 < -(x * φ x) := by have := phi_neg E hx0; nlinarith
  have := hu x (Ioo_subset_Icc_self hx)
  exact div_pos (mul_pos hv (by linarith)) hx0

end

set_option maxHeartbeats 4000000 in
theorem bands (w φ : ℝ → ℝ)
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
    1.664155 ≤ ζ 1 ^ 2 * Real.exp (w (ζ 1)) ∧ ζ 1 ^ 2 * Real.exp (w (ζ 1)) ≤ 1.664157 ∧
      2.10852 ≤ ζ 2 ^ 2 * Real.exp (w (ζ 2)) ∧ ζ 2 ^ 2 * Real.exp (w (ζ 2)) ≤ 2.10858 := by
  have E := hyp_of hw hφ0 hφ
  have hsub : Icc (0 : ℝ) (41 / 10) ⊆ Ici 0 := fun t ht => ht.1
  obtain ⟨-, hdec, hEA, hφA, hφB⟩ := Checked.Math.GCerts.chain (w := w) (φ := φ)
    (fun s hs => (hw s hs.1).mono hsub) (hφ0.mono hsub)
    (fun s hs => (hφ s hs.1).mono hsub) h0
  rw [abs_le] at hEA hφA hφB
  -- the homology variables
  set Uf : ℝ → ℝ := fun x => x * Real.exp (w x) / -φ x with hUf
  set Vf : ℝ → ℝ := fun x => -(x * φ x) with hVf
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
  obtain ⟨f1, f4, f2, f3, -, eV⟩ := Work.Math.GLamChain.chain hu hv hU0 hV0
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
  -- values: λ = 2u at a zero of v − 2
  have z1pos : 0 < z1 := by linarith [z1mem.1]
  have z2pos : 0 < z2 := by linarith [z2mem.1]
  have k1 := at_zero_U E z1pos (by rw [hYV, hVz1]; ring)
  have k2 := at_zero_U E z2pos (by rw [hYV, hVz2]; ring)
  have b1 := u4 z1 z1mem
  have b2 := u3 z2 z2mem
  have l1 : ζ 1 ^ 2 * Real.exp (w (ζ 1)) = 2 * Uf z1 := by
    rw [e1]; have : U w φ z1 = Uf z1 := rfl; rw [← this, k1]; unfold lam; ring
  have l2 : ζ 2 ^ 2 * Real.exp (w (ζ 2)) = 2 * Uf z2 := by
    rw [e2]; have : U w φ z2 = Uf z2 := rfl; rw [← this, k2]; unfold lam; ring
  rw [l1, l2]
  norm_num
  refine ⟨by linarith [b1.2.1], by linarith [b1.2.2], by linarith [b2.2.1], by linarith [b2.2.2]⟩

end Work.Math.GLamBands
