import Checked.Math.BEAllMain
import Work.Math.BEMonoExt

/-! Bonnor–Ebert sphere, `BEMonoMain`: the assembly of `Checked.Math.BEAllMain.main` repeated with the monotone
segments of the mass: strictly increasing up to the first maximum, and strictly monotone between consecutive
extrema (certified part from `Work.Math.BEMonoExt.main_mono`, tail segments from `BEFocus.tail`, the
segment from the third maximum to the first tail zero as in `BEAllMain`). -/

namespace Work.Math.BEMonoMain
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEAllMain

set_option maxHeartbeats 4000000 in
/-- `Checked.Math.BEAllMain.main` (copied) with the monotone segments of the mass between consecutive extrema:
the assembly behind `Work.Math.BonnorEbertMono.bonnor_ebert_extrema_monotone`. -/
theorem main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) <
          ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) / Real.sqrt (4 * Real.pi)) ∧
      Tendsto (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) atTop
        (𝓝 (Real.sqrt (2 / Real.pi))) ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) := by
  -- φ < 0 from radius 7 on
  have φneg : ∀ s, 7 ≤ s → φ s < 0 := by
    intro s hs
    obtain ⟨r1, r2, r3⟩ := restrict (max s 300000) hw hφ0 hφ
    exact (Checked.Math.BEState300.state300 (max s 300000) (le_max_right _ _) w φ r1 r2 r3 h0).1 s
      ⟨hs, le_max_left _ _⟩
  obtain ⟨r1, r2, r3⟩ := restrict 300000 hw hφ0 hφ
  obtain ⟨-, su, sv, sg⟩ := Checked.Math.BEState300.state300 300000 le_rfl w φ r1 r2 r3 h0
  obtain ⟨ξ₁, ξ₂, ξ₃, ξ₄, ξ₅, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hmax, hmin, hmax2, hmin2,
    hmax3, M5lo, -, -, -, m4hi, Panti5, Mm1, Ma12, Mm23, Ma34, Mm45⟩ :=
    Work.Math.BEMonoExt.main_mono 300000 le_rfl w φ r1 r2 r3 h0
  norm_num at a3 a4 a5 a6 a7 a8 a9 a10
  -- derivatives
  have dws : ∀ t : ℝ, 0 < t →
      HasDerivAt w (φ t) t ∧ HasDerivAt φ (-(2 / t * φ t) - Real.exp (w t)) t := fun t ht =>
    ⟨(hw t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht), (hφ t ht).hasDerivAt (Ici_mem_nhds ht)⟩
  have dUV : ∀ t : ℝ, 7 ≤ t →
      HasDerivAt (Uf w φ) (Uf w φ t * (3 - Uf w φ t - Vf w φ t) / t) t ∧
      HasDerivAt (Vf w φ) (Vf w φ t * (Uf w φ t - 1) / t) t := fun t ht =>
    Checked.Math.BEHMain.homology_deriv_at (by linarith) (φneg t ht) (dws t (by linarith)).1
      (dws t (by linarith)).2
  have dP : ∀ t ∈ Ici (7 : ℝ), HasDerivAt (Pf w φ) (Pf w φ t * (2 * Uf w φ t - Vf w φ t) / t) t := by
    intro t ht
    obtain ⟨d1, d2⟩ := dUV t ht
    have ht0 : 0 < t := by linarith [mem_Ici.1 ht]
    have hd : HasDerivAt (fun s => Uf w φ s * Vf w φ s ^ 3)
        (Uf w φ t * (3 - Uf w φ t - Vf w φ t) / t * Vf w φ t ^ 3 +
          Uf w φ t * (↑3 * Vf w φ t ^ (3 - 1) * (Vf w φ t * (Uf w φ t - 1) / t))) t :=
      d1.mul (d2.pow 3)
    refine hd.congr_deriv ?_
    unfold Pf
    field_simp; ring
  have UVpos7 : ∀ t : ℝ, 7 ≤ t → 0 < Uf w φ t ∧ 0 < Vf w φ t := by
    intro t ht
    have h1 := φneg t ht
    have h2 := Real.exp_pos (w t)
    have h3 : (0 : ℝ) < t := by linarith
    refine ⟨div_pos (by positivity) (by linarith), ?_⟩
    show 0 < -(t * φ t)
    nlinarith
  have Ppos : ∀ t ∈ Ici (7 : ℝ), 0 < Pf w φ t := fun t ht => by
    obtain ⟨h1, h2⟩ := UVpos7 t ht
    unfold Pf; positivity
  have Mlt : ∀ s t : ℝ, 7 ≤ s → 7 ≤ t → Pf w φ s < Pf w φ t → Mf w φ s < Mf w φ t :=
    fun s t hs ht h => Checked.Math.BEHMain.mass_lt (by linarith) (φneg s hs) (by linarith) (φneg t ht) h
  -- the analytic tail from radius 300000
  have su' : |Uf w φ 300000 - 998005545 / 1000000000| ≤ 4 / 10000000 := su
  have sv' : |Vf w φ 300000 - 2002054156 / 1000000000| ≤ 4 / 10000000 := sv
  obtain ⟨N0le, N0pos⟩ := N0_bounds su' sv'
  have hg0 : 2 * Uf w φ 300000 - Vf w φ 300000 < 0 := sg 300000 ⟨by norm_num, le_rfl⟩
  obtain ⟨ζ, hζ, hT, hζ0, gneg0, gz, gpos, gneg, Uside, Udec, Nz, -, Ulim, Vlim⟩ :=
    Checked.Math.BEFocus.tail (U := Uf w φ) (V := Vf w φ) (s0 := 300000) (by norm_num)
      (fun t ht => (dUV t (by linarith [mem_Ici.1 ht])).1)
      (fun t ht => (dUV t (by linarith [mem_Ici.1 ht])).2) (by linarith) N0pos hg0
  have ζbig : ∀ k, 300000 < ζ k := fun k => lt_of_lt_of_le hζ0 (hζ.monotone (Nat.zero_le k))
  have ζ7 : ∀ k, (7 : ℝ) ≤ ζ k := fun k => by linarith [ζbig k]
  have Uw : ∀ k, 989 / 990 ≤ Uf w φ (ζ k) ∧ Uf w φ (ζ k) ≤ 991 / 990 := fun k => U_win N0le (Nz k)
  have Pz : ∀ k, Pf w φ (ζ k) = 8 * Uf w φ (ζ k) ^ 4 := by
    intro k
    have h := gz k
    have hv : Vf w φ (ζ k) = 2 * Uf w φ (ζ k) := by linarith
    unfold Pf; rw [hv]; ring
  have Upos : ∀ k, 0 < Uf w φ (ζ k) := fun k => by linarith [(Uw k).1]
  -- the values at the zeros
  obtain ⟨vmin, vmax, vsep⟩ := vals (Uz := fun k => Uf w φ (ζ k)) Upos Uside Udec
  have hminv : StrictMono (fun m => Pf w φ (ζ (2 * m))) := by
    have e : (fun m => Pf w φ (ζ (2 * m))) = fun m => 8 * Uf w φ (ζ (2 * m)) ^ 4 :=
      funext fun m => Pz _
    rw [e]; exact vmin
  have hmaxv : StrictAnti (fun m => Pf w φ (ζ (2 * m + 1))) := by
    have e : (fun m => Pf w φ (ζ (2 * m + 1))) = fun m => 8 * Uf w φ (ζ (2 * m + 1)) ^ 4 :=
      funext fun m => Pz _
    rw [e]; exact vmax
  have hsep : ∀ m j, Pf w φ (ζ (2 * m)) < Pf w φ (ζ (2 * j + 1)) := fun m j => by
    rw [Pz, Pz]; exact vsep m j
  -- monotonicity on the segments
  have dPI : ∀ a b : ℝ, 7 ≤ a → ∀ t ∈ Icc a b,
      HasDerivAt (Pf w φ) (Pf w φ t * (2 * Uf w φ t - Vf w φ t) / t) t :=
    fun a b ha t ht => dP t (mem_Ici.2 (ha.trans ht.1))
  have PposI : ∀ a b : ℝ, 7 ≤ a → ∀ t ∈ Icc a b, 0 < Pf w φ t :=
    fun a b ha t ht => Ppos t (mem_Ici.2 (ha.trans ht.1))
  have hmono : ∀ k, StrictMonoOn (Pf w φ) (Icc (ζ (2 * k)) (ζ (2 * k + 1))) := fun k =>
    P_mono_of_pos (g := fun t => 2 * Uf w φ t - Vf w φ t) (by linarith [ζ7 (2 * k)])
      (hζ.monotone (by omega)) (dPI _ _ (ζ7 _)) (PposI _ _ (ζ7 _)) (gpos k)
  have hanti : ∀ k, StrictAntiOn (Pf w φ) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2))) := fun k =>
    P_anti_of_neg (g := fun t => 2 * Uf w φ t - Vf w φ t) (by linarith [ζ7 (2 * k + 1)])
      (hζ.monotone (by omega)) (dPI _ _ (ζ7 _)) (PposI _ _ (ζ7 _)) (gneg k)
  have anti0 : StrictAntiOn (Pf w φ) (Icc 300000 (ζ 0)) :=
    P_anti_of_neg (g := fun t => 2 * Uf w φ t - Vf w φ t) (by norm_num) (ζbig 0).le
      (dPI _ _ (by norm_num)) (PposI _ _ (by norm_num)) (fun t ht => gneg0 t ⟨ht.1.le, ht.2⟩)
  obtain ⟨E1, E2, E3, E4⟩ := envelope hζ hT hmono hanti hminv hmaxv hsep
  -- from the third maximum to the first tail zero
  have Panti5' : StrictAntiOn (Pf w φ) (Icc ξ₅ 300000) := Panti5
  have PA : StrictAntiOn (Pf w φ) (Icc ξ₅ (ζ 0)) := by
    intro x hx y hy hxy
    rcases le_or_gt y 300000 with hy3 | hy3
    · exact Panti5' ⟨hx.1, by linarith⟩ ⟨hy.1, hy3⟩ hxy
    rcases le_or_gt 300000 x with hx3 | hx3
    · exact anti0 ⟨hx3, hx.2⟩ ⟨hy3.le, hy.2⟩ hxy
    · have h1 := anti0 ⟨le_rfl, (ζbig 0).le⟩ ⟨hy3.le, hy.2⟩ hy3
      have h2 := Panti5'.antitoneOn ⟨hx.1, hx3.le⟩ ⟨by linarith [hx.1], le_rfl⟩ hx3.le
      linarith
  have h5lo : (84497 : ℝ) ≤ ξ₅ := a9
  have h5hi : ξ₅ ≤ 84516 := a10
  have ξ57 : (7 : ℝ) ≤ ξ₅ := by linarith
  have ξ47 : (7 : ℝ) ≤ ξ₄ := by linarith
  have Pξ5 : 0.80091 ^ 2 * (4 * Real.pi) ≤ Pf w φ ξ₅ :=
    P_lt_of_M (by linarith) (φneg ξ₅ ξ57) (by norm_num) M5lo
  have Pξ4 : Pf w φ ξ₄ ≤ 0.787995 ^ 2 * (4 * Real.pi) :=
    P_le_of_M (by linarith) (φneg ξ₄ ξ47) m4hi
  have Pζ1 : Pf w φ (ζ 1) ≤ 8 * (991 / 990 : ℝ) ^ 4 := by
    rw [Pz]
    have := pow_le_pow_left₀ (Upos 1).le (Uw 1).2 4
    linarith
  have Pζ0 : 8 * (989 / 990 : ℝ) ^ 4 ≤ Pf w φ (ζ 0) := by
    rw [Pz]
    have := pow_le_pow_left₀ (by norm_num) (Uw 0).1 4
    linarith
  have chi := const_hi
  have clo := const_lo
  have T1 : ∀ s : ℝ, 300000 < s → Pf w φ s < Pf w φ ξ₅ := by
    intro s hs
    rcases le_or_gt s (ζ 0) with h | h
    · exact PA ⟨le_rfl, by linarith⟩ ⟨by linarith, h⟩ (by linarith)
    · have := E4 s h.le
      linarith
  have T2 : ∀ s : ℝ, 300000 ≤ s → Pf w φ ξ₄ < Pf w φ s := by
    intro s hs
    have : Pf w φ (ζ 0) ≤ Pf w φ s := by
      rcases le_or_gt s (ζ 0) with h | h
      · exact PA.antitoneOn ⟨by linarith, h⟩ ⟨by linarith [ζbig 0], le_rfl⟩ h
      · exact E3 s h.le
    linarith
  have ξ4lo : (15699 / 2 : ℝ) ≤ ξ₄ := by linarith
  have ξ4hi : ξ₄ ≤ 31399 / 4 := by linarith
  have cb := c_bounds
  -- the mass at the certified extrema relative to √(2/π)
  have M5gt : Real.sqrt (2 / Real.pi) < Mf w φ ξ₅ := by
    have : (0.80091 : ℝ) ≤ Mf w φ ξ₅ := M5lo
    linarith [cb.2]
  have M4lt : Mf w φ ξ₄ < Real.sqrt (2 / Real.pi) := by
    have : Mf w φ ξ₄ ≤ 0.787995 := m4hi
    linarith [cb.1]
  have M51 : Mf w φ ξ₅ < Mf w φ ξ₁ := hmax ξ₅ ⟨by linarith, by linarith⟩ (by
    intro h; norm_num at a1 a2; linarith)
  have M53 : Mf w φ ξ₅ < Mf w φ ξ₃ := hmax2 ξ₅ ⟨by linarith, by linarith⟩ (by intro h; linarith)
  have M24 : Mf w φ ξ₂ < Mf w φ ξ₄ := hmin ξ₄ ⟨by norm_num at a1 a2; linarith, by linarith⟩
    (by intro h; linarith)
  have tM : ∀ a b : ℝ, 7 ≤ a → StrictMonoOn (Pf w φ) (Icc a b) → StrictMonoOn (Mf w φ) (Icc a b) :=
    fun a b ha h x hx y hy hxy => Mlt x y (ha.trans hx.1) (ha.trans hy.1) (h hx hy hxy)
  have tA : ∀ a b : ℝ, 7 ≤ a → StrictAntiOn (Pf w φ) (Icc a b) → StrictAntiOn (Mf w φ) (Icc a b) :=
    fun a b ha h x hx y hy hxy => Mlt y x (ha.trans hy.1) (ha.trans hx.1) (h hx hy hxy)
  refine ⟨seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ, ?_, ?_, a1, a2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => show ξ₁ < ξ₂; norm_num at a1 a2; linarith
    | 1 => show ξ₂ < ξ₃; linarith
    | 2 => show ξ₃ < ξ₄; linarith
    | 3 => show ξ₄ < ξ₅; linarith
    | 4 => show ξ₅ < ζ 0; linarith [ζbig 0]
    | k + 5 => show ζ k < ζ (k + 1); exact hζ (Nat.lt_succ_self k)
  · rw [← Filter.tendsto_add_atTop_iff_nat 5]
    exact hT
  · intro s hs hne
    show Mf w φ s < Mf w φ ξ₁
    rcases le_or_gt s 300000 with h | h
    · exact hmax s ⟨hs, h⟩ hne
    · exact (Mlt s ξ₅ (by linarith) ξ57 (T1 s h)).trans M51
  · intro k
    match k with
    | 0 =>
      intro s hs hne
      show Mf w φ ξ₂ < Mf w φ s
      have hs' : ξ₁ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmin s ⟨hs', h⟩ hne
      · exact M24.trans (Mlt ξ₄ s ξ47 (by linarith) (T2 s h.le))
    | 1 =>
      intro s hs hne
      show Mf w φ ξ₄ < Mf w φ s
      have hs' : ξ₃ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmin2 s ⟨hs', h⟩ hne
      · exact Mlt ξ₄ s ξ47 (by linarith) (T2 s h.le)
    | 2 =>
      intro s hs hne
      show Mf w φ (ζ 0) < Mf w φ s
      have hs' : ξ₅ ≤ s := hs
      have hne' : s ≠ ζ 0 := hne
      apply Mlt (ζ 0) s (ζ7 0) (by linarith)
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · exact PA ⟨hs', hlt.le⟩ ⟨by linarith [ζbig 0], le_rfl⟩ hlt
      rcases le_or_gt s (ζ 1) with h1 | h1
      · exact hmono 0 ⟨le_rfl, (hζ (by norm_num : 0 < 1)).le⟩ ⟨hgt.le, h1⟩ hgt
      · have h02 : Pf w φ (ζ 0) < Pf w φ (ζ 2) := hminv (show 0 < 1 by norm_num)
        rcases eq_or_ne s (ζ 2) with he | he
        · rw [he]; exact h02
        · exact h02.trans (E2 0 s h1.le he)
    | i + 3 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3)) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 3) = (2 * i + 1) + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3) + 1) = ζ (2 * i + 2) := by
        rw [show 2 * (i + 3) + 1 = (2 * i + 2) + 5 by ring]; rfl
      rw [e1, e2]
      intro s hs hne
      exact Mlt _ s (ζ7 _) (by linarith [ζ7 (2 * i + 1), mem_Ici.1 hs]) (E2 i s hs hne)
  · intro k
    match k with
    | 0 =>
      intro s hs hne
      show Mf w φ s < Mf w φ ξ₃
      have hs' : ξ₂ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmax2 s ⟨hs', h⟩ hne
      · exact (Mlt s ξ₅ (by linarith) ξ57 (T1 s h)).trans M53
    | 1 =>
      intro s hs hne
      show Mf w φ s < Mf w φ ξ₅
      have hs' : ξ₄ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmax3 s ⟨hs', h⟩ hne
      · exact Mlt s ξ₅ (by linarith) ξ57 (T1 s h)
    | i + 2 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 2) + 1) = ζ (2 * i) := by
        rw [show 2 * (i + 2) + 1 = 2 * i + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 2) + 2) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 2) + 2 = (2 * i + 1) + 5 by ring]; rfl
      rw [e1, e2]
      intro s hs hne
      exact Mlt s _ (by linarith [ζ7 (2 * i), mem_Ici.1 hs]) (ζ7 _) (E1 i s hs hne)
  · intro k
    match k with
    | 0 => exact ⟨(M24.trans M4lt : Mf w φ ξ₂ < _), (M5gt.trans M51 : _ < Mf w φ ξ₁)⟩
    | 1 => exact ⟨(M4lt : Mf w φ ξ₄ < _), (M5gt.trans M53 : _ < Mf w φ ξ₃)⟩
    | 2 =>
      refine ⟨?_, (M5gt : _ < Mf w φ ξ₅)⟩
      show Mf w φ (ζ 0) < _
      apply (band (by linarith [ζ7 0]) (φneg _ (ζ7 0))).1
      rw [Pz]
      have s1 : Uf w φ (ζ 0) < 1 := (Uside 0).1
      have h1 : Uf w φ (ζ 0) ^ 4 < 1 := pow_lt_one₀ (Upos _).le s1 (by norm_num)
      linarith
    | i + 3 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3) + 1) = ζ (2 * (i + 1)) := by
        rw [show 2 * (i + 3) + 1 = 2 * (i + 1) + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3)) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 3) = (2 * i + 1) + 5 by ring]; rfl
      rw [e1, e2]
      constructor
      · apply (band (by linarith [ζ7 (2 * (i + 1))]) (φneg _ (ζ7 _))).1
        rw [Pz]
        have h1 : Uf w φ (ζ (2 * (i + 1))) ^ 4 < 1 :=
          pow_lt_one₀ (Upos _).le (Uside (i + 1)).1 (by norm_num)
        linarith
      · apply (band (by linarith [ζ7 (2 * i + 1)]) (φneg _ (ζ7 _))).2
        rw [Pz]
        have h2 : 1 < Uf w φ (ζ (2 * i + 1)) ^ 4 := one_lt_pow₀ (Uside i).2 (by norm_num)
        linarith
  · -- the limit
    have hPl : Tendsto (Pf w φ) atTop (𝓝 (1 * 2 ^ 3)) := Ulim.mul (Vlim.pow 3)
    have hl : Tendsto (fun s => Real.sqrt (Pf w φ s / (4 * Real.pi))) atTop
        (𝓝 (Real.sqrt (1 * 2 ^ 3 / (4 * Real.pi)))) :=
      (hPl.div_const (4 * Real.pi)).sqrt
    have hv : Real.sqrt (1 * 2 ^ 3 / (4 * Real.pi)) = Real.sqrt (2 / Real.pi) := by
      congr 1; have := Real.pi_pos; field_simp; ring
    rw [hv] at hl
    refine hl.congr' ?_
    filter_upwards [eventually_ge_atTop (7 : ℝ)] with s hs
    exact (M_eq (by linarith) (φneg s hs)).symm
  · show StrictMonoOn _ (Icc 0 ξ₁)
    exact Mm1
  · intro k
    match k with
    | 0 =>
      show StrictAntiOn _ (Icc ξ₁ ξ₂)
      exact Ma12
    | 1 =>
      show StrictAntiOn _ (Icc ξ₃ ξ₄)
      exact Ma34
    | 2 =>
      show StrictAntiOn (Mf w φ) (Icc ξ₅ (ζ 0))
      exact tA _ _ ξ57 PA
    | i + 3 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3)) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 3) = (2 * i + 1) + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3) + 1) = ζ (2 * i + 2) := by
        rw [show 2 * (i + 3) + 1 = (2 * i + 2) + 5 by ring]; rfl
      rw [e1, e2]
      exact tA _ _ (ζ7 _) (hanti i)
  · intro k
    match k with
    | 0 =>
      show StrictMonoOn _ (Icc ξ₂ ξ₃)
      exact Mm23
    | 1 =>
      show StrictMonoOn _ (Icc ξ₄ ξ₅)
      exact Mm45
    | i + 2 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 2) + 1) = ζ (2 * i) := by
        rw [show 2 * (i + 2) + 1 = 2 * i + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 2) + 2) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 2) + 2 = (2 * i + 1) + 5 by ring]; rfl
      rw [e1, e2]
      exact tM _ _ (ζ7 _) (hmono i)

end Work.Math.BEMonoMain
