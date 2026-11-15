import Checked.Math.GExistsLeft

/-! Bonnor–Ebert sphere, `BEGlobalExists`: the regular solution of the isothermal equation w'' + (2/s) w' + e^w = 0, w(0) = 0, exists on the whole half-line (one-sided derivatives within it, φ = w' continuous at the centre). Route: the left part of `Checked.Math.GExistsLeft.exists_left`, then the right parts of `Checked.Math.GExistsRight.exists_right` on longer and longer intervals, which agree on their common interval by uniqueness of the regular ODE (`ODE_solution_unique_of_mem_Icc_right`); the global right part takes at t the solution with index ⌈t⌉₊. Promoted from `Work/Math/BEGlobalExists.lean`. -/

namespace Checked.Math.BEGlobalExists
open Set Filter Topology

/-- The (unclamped) field in (w, φ). -/
noncomputable def G (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -(2 / t * p.2) - Real.exp p.1)

theorem lipG {M t : ℝ} (ht : 1 / 2 ≤ t) :
    LipschitzOnWith (Real.toNNReal (5 + Real.exp M)) (G t) {p : ℝ × ℝ | p.1 ≤ M} := by
  have ht0 : 0 < t := by linarith
  have hK : (0 : ℝ) ≤ 5 + Real.exp M := by positivity
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ hK]
  simp only [G, Prod.dist_eq, Real.dist_eq]
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hm0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := (abs_nonneg _).trans hd1
  have hE := Real.exp_pos M
  refine max_le ?_ ?_
  · nlinarith
  · have e : -(2 / t * p.2) - Real.exp p.1 - (-(2 / t * q.2) - Real.exp q.1) =
        -(2 / t * (p.2 - q.2)) - (Real.exp p.1 - Real.exp q.1) := by ring
    rw [e]
    have h1 := Checked.Math.GExistsRight.exp_sub_le_of_le (m := M) hp hq
    have h2 : |2 / t * (p.2 - q.2)| ≤ 4 * |p.2 - q.2| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / t)]
      have : 2 / t ≤ 4 := by rw [div_le_iff₀ ht0]; linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    calc |-(2 / t * (p.2 - q.2)) - (Real.exp p.1 - Real.exp q.1)|
        ≤ |2 / t * (p.2 - q.2)| + |Real.exp p.1 - Real.exp q.1| := by
          rw [sub_eq_add_neg]
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg, abs_neg]
      _ ≤ 4 * max |p.1 - q.1| |p.2 - q.2| + Real.exp M * max |p.1 - q.1| |p.2 - q.2| := by
          gcongr
          · linarith
          · exact h1.trans (mul_le_mul_of_nonneg_left hd1 hE.le)
      _ ≤ (5 + Real.exp M) * max |p.1 - q.1| |p.2 - q.2| := by nlinarith

/-- Uniqueness of the right part on [1/2, T]. -/
theorem uniq {T : ℝ} {w1 φ1 w2 φ2 : ℝ → ℝ}
    (h1 : ∀ t ∈ Icc (1 / 2 : ℝ) T, HasDerivWithinAt w1 (φ1 t) (Icc (1 / 2) T) t ∧
        HasDerivWithinAt φ1 (-(2 / t * φ1 t) - Real.exp (w1 t)) (Icc (1 / 2) T) t)
    (h2 : ∀ t ∈ Icc (1 / 2 : ℝ) T, HasDerivWithinAt w2 (φ2 t) (Icc (1 / 2) T) t ∧
        HasDerivWithinAt φ2 (-(2 / t * φ2 t) - Real.exp (w2 t)) (Icc (1 / 2) T) t)
    (hw : w1 (1 / 2) = w2 (1 / 2)) (hφ : φ1 (1 / 2) = φ2 (1 / 2)) :
    ∀ t ∈ Icc (1 / 2 : ℝ) T, w1 t = w2 t ∧ φ1 t = φ2 t := by
  set f : ℝ → ℝ × ℝ := fun t => (w1 t, φ1 t) with hf
  set g : ℝ → ℝ × ℝ := fun t => (w2 t, φ2 t) with hg
  have df : ∀ t ∈ Icc (1 / 2 : ℝ) T, HasDerivWithinAt f (G t (f t)) (Icc (1 / 2) T) t :=
    fun t ht => (h1 t ht).1.prodMk (h1 t ht).2
  have dg : ∀ t ∈ Icc (1 / 2 : ℝ) T, HasDerivWithinAt g (G t (g t)) (Icc (1 / 2) T) t :=
    fun t ht => (h2 t ht).1.prodMk (h2 t ht).2
  have cf : ContinuousOn f (Icc (1 / 2) T) := fun t ht => (df t ht).continuousWithinAt
  have cg : ContinuousOn g (Icc (1 / 2) T) := fun t ht => (dg t ht).continuousWithinAt
  have c1 : ContinuousOn w1 (Icc (1 / 2) T) := fun t ht => (h1 t ht).1.continuousWithinAt
  have c2 : ContinuousOn w2 (Icc (1 / 2) T) := fun t ht => (h2 t ht).1.continuousWithinAt
  obtain ⟨M1, hM1⟩ := (isCompact_Icc.bddAbove_image c1)
  obtain ⟨M2, hM2⟩ := (isCompact_Icc.bddAbove_image c2)
  set M := max M1 M2
  have hv : ∀ t ∈ Ico (1 / 2 : ℝ) T,
      LipschitzOnWith (Real.toNNReal (5 + Real.exp M)) (G t) {p : ℝ × ℝ | p.1 ≤ M} :=
    fun t ht => lipG ht.1
  have toIci : ∀ {F : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {t : ℝ}, t ∈ Ico (1 / 2 : ℝ) T →
      HasDerivWithinAt F d (Icc (1 / 2) T) t → HasDerivWithinAt F d (Ici t) t := by
    intro F d t ht h
    refine h.mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨Iio T, isOpen_Iio, ht.2, ?_⟩)
    intro y hy; exact ⟨le_trans ht.1 hy.2, le_of_lt hy.1⟩
  have e := ODE_solution_unique_of_mem_Icc_right (v := G) (s := fun _ => {p : ℝ × ℝ | p.1 ≤ M})
    (f := f) (g := g) (a := 1 / 2) (b := T) hv cf
    (fun t ht => toIci ht (df t (Ico_subset_Icc_self ht)))
    (fun t ht => le_trans (hM1 ⟨t, Ico_subset_Icc_self ht, rfl⟩) (le_max_left _ _)) cg
    (fun t ht => toIci ht (dg t (Ico_subset_Icc_self ht)))
    (fun t ht => le_trans (hM2 ⟨t, Ico_subset_Icc_self ht, rfl⟩) (le_max_right _ _))
    (by simp only [hf, hg, hw, hφ])
  intro t ht
  have := e ht
  simp only [hf, hg, Prod.mk.injEq] at this
  exact this

theorem exists_global : ∃ w φ : ℝ → ℝ,
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧
    (∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s) ∧
    w 0 = 0 := by
  obtain ⟨wL, φL, h0, hcφ, hwb, hφb, hφb', hdw, hdφ⟩ := Checked.Math.GExistsLeft.exists_left
  have hT : ∀ n : ℕ, (1 / 2 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  choose W Φ hW0 hΦ0 hD using fun n : ℕ =>
    Checked.Math.GExistsRight.exists_right ((n : ℝ) + 1) _ _ (hT n) hwb hφb hφb'
  -- agreement of the right parts
  have agree : ∀ a b : ℕ, a ≤ b → ∀ t ∈ Icc (1 / 2 : ℝ) ((a : ℝ) + 1),
      W a t = W b t ∧ Φ a t = Φ b t := by
    intro a b hab
    have hsub : Icc (1 / 2 : ℝ) ((a : ℝ) + 1) ⊆ Icc (1 / 2) ((b : ℝ) + 1) :=
      Icc_subset_Icc le_rfl (by have : (a : ℝ) ≤ b := Nat.cast_le.2 hab; linarith)
    refine uniq (hD a) (fun t ht => ⟨((hD b t (hsub ht)).1).mono hsub,
      ((hD b t (hsub ht)).2).mono hsub⟩) ((hW0 a).trans (hW0 b).symm) ((hΦ0 a).trans (hΦ0 b).symm)
  -- the global right part
  set wR : ℝ → ℝ := fun t => W ⌈t⌉₊ t with hwR
  set φR : ℝ → ℝ := fun t => Φ ⌈t⌉₊ t with hφR
  -- near t, the global right part is the solution of index ⌈t⌉₊
  have near : ∀ t : ℝ, 1 / 2 ≤ t → ∀ s ∈ Icc (1 / 2 : ℝ) ((⌈t⌉₊ : ℝ) + 1),
      wR s = W ⌈t⌉₊ s ∧ φR s = Φ ⌈t⌉₊ s := by
    intro t _ s hs
    have hsc : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    rcases le_total ⌈s⌉₊ ⌈t⌉₊ with h | h
    · have hs' : s ∈ Icc (1 / 2 : ℝ) ((⌈s⌉₊ : ℝ) + 1) := ⟨hs.1, by linarith⟩
      exact agree _ _ h s hs'
    · have := agree _ _ h s hs
      exact ⟨this.1.symm, this.2.symm⟩
  have dR : ∀ t : ℝ, 1 / 2 ≤ t →
      HasDerivWithinAt wR (φR t) (Ici (1 / 2)) t ∧
      HasDerivWithinAt φR (-(2 / t * φR t) - Real.exp (wR t)) (Ici (1 / 2)) t := by
    intro t ht
    have nr := near t ht
    set n := ⌈t⌉₊
    have htn : t < (n : ℝ) + 1 := by have := Nat.le_ceil t; linarith
    have hmem : Icc (1 / 2 : ℝ) ((n : ℝ) + 1) ∈ 𝓝[Ici (1 / 2)] t :=
      mem_nhdsWithin.2 ⟨Iio ((n : ℝ) + 1), isOpen_Iio, htn,
        fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
    have ht' : t ∈ Icc (1 / 2 : ℝ) ((n : ℝ) + 1) := ⟨ht, htn.le⟩
    have ew : wR =ᶠ[𝓝[Ici (1 / 2)] t] W n :=
      Filter.mem_of_superset hmem fun s hs => (nr s hs).1
    have eφ : φR =ᶠ[𝓝[Ici (1 / 2)] t] Φ n :=
      Filter.mem_of_superset hmem fun s hs => (nr s hs).2
    have vw : wR t = W n t := (nr t ht').1
    have vφ : φR t = Φ n t := (nr t ht').2
    obtain ⟨d1, d2⟩ := hD n t ht'
    refine ⟨?_, ?_⟩
    · rw [vφ]; exact (d1.mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ew vw
    · rw [vφ, vw]; exact (d2.mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq eφ vφ
  have wR0 : wR (1 / 2) = wL (1 / 2) := by
    simp only [hwR]; exact hW0 _
  have φR0 : φR (1 / 2) = φL (1 / 2) := by
    simp only [hφR]; exact hΦ0 _
  -- glue at 1/2
  set w : ℝ → ℝ := fun y => if y ≤ 1 / 2 then wL y else wR y with hw
  set φ : ℝ → ℝ := fun y => if y ≤ 1 / 2 then φL y else φR y with hφ
  have eL : ∀ y, y ≤ 1 / 2 → w y = wL y ∧ φ y = φL y := fun y h => by
    rw [hw, hφ]; exact ⟨if_pos h, if_pos h⟩
  have eR : ∀ y, 1 / 2 ≤ y → w y = wR y ∧ φ y = φR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hw, hφ]; exact ⟨(if_pos le_rfl).trans wR0.symm, (if_pos le_rfl).trans φR0.symm⟩
    · rw [hw, hφ]; exact ⟨if_neg (not_le.2 h), if_neg (not_le.2 h)⟩
  -- generic gluing of one-sided derivatives
  have glue : ∀ (F FL FR : ℝ → ℝ) (d : ℝ) (x : ℝ), 0 ≤ x →
      (∀ y, y ≤ 1 / 2 → F y = FL y) → (∀ y, 1 / 2 ≤ y → F y = FR y) →
      (x ≤ 1 / 2 → HasDerivWithinAt FL d (Icc 0 (1 / 2)) x) →
      (1 / 2 ≤ x → HasDerivWithinAt FR d (Ici (1 / 2)) x) →
      HasDerivWithinAt F d (Ici 0) x := by
    intro F FL FR d x hx hL hR dL dR'
    have dL' : x ≤ 1 / 2 → HasDerivWithinAt F d (Icc 0 (1 / 2)) x := fun h =>
      (dL h).congr (fun y hy => hL y hy.2) (hL x h)
    have dR'' : 1 / 2 ≤ x → HasDerivWithinAt F d (Ici (1 / 2)) x := fun h =>
      (dR' h).congr (fun y hy => hR y hy) (hR x h)
    rcases lt_trichotomy x (1 / 2) with h | h | h
    · exact (dL' h.le).mono_of_mem_nhdsWithin
        (mem_nhdsWithin.2 ⟨Iio (1 / 2), isOpen_Iio, h, fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩)
    · have hu : Ici (0 : ℝ) = Icc 0 (1 / 2) ∪ Ici (1 / 2) := by
        rw [Icc_union_Ici_eq_Ici (by norm_num)]
      rw [hu]
      exact (dL' h.le).union (dR'' h.ge)
    · exact (dR'' h.le).mono_of_mem_nhdsWithin
        (mem_nhdsWithin.2 ⟨Ioi (1 / 2), isOpen_Ioi, h, fun y hy => mem_Ici.2 (le_of_lt hy.1)⟩)
  refine ⟨w, φ, fun s hs => ?_, ?_, fun s hs => ?_, (eL 0 (by norm_num)).1.trans h0⟩
  · refine glue w wL wR (φ s) s hs (fun y h => (eL y h).1) (fun y h => (eR y h).1)
      (fun h => by rw [(eL s h).2]; exact hdw s ⟨hs, h⟩)
      (fun h => by rw [(eR s h).2]; exact (dR s h).1)
  · have e : φ =ᶠ[𝓝[Ici 0] 0] φL := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
        with y hy using (eL y (le_of_lt hy)).2
    exact (hcφ.continuousWithinAt).congr_of_eventuallyEq e (eL 0 (by norm_num)).2
  · have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    refine glue φ φL φR _ s hs0 (fun y h => (eL y h).2) (fun y h => (eR y h).2)
      (fun h => by rw [(eL s h).1, (eL s h).2]; exact hdφ s ⟨hs, h⟩)
      (fun h => by rw [(eR s h).1, (eR s h).2]; exact (dR s h).2)

end Checked.Math.BEGlobalExists
