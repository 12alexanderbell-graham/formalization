import Mathlib

/-! Run 2026-11-09T0828Z (from the scratch file of fork A): Crocco map for the adverse pressure sign. -/

namespace Work.FalknerSkan.NegCrocco
open Set

/-- The Crocco change of variables t = p(η), pressure term `+ 1 - p²` (β < 0 after scaling). -/
theorem crocco_pos {k E : ℝ} (hE : 0 < E) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Icc 0 E, HasDerivWithinAt f (p η) (Icc 0 E) η)
    (hp : ∀ η ∈ Icc 0 E, HasDerivWithinAt p (q η) (Icc 0 E) η)
    (hq : ∀ η ∈ Icc 0 E, HasDerivWithinAt q (-(k * f η * q η) + 1 - p η ^ 2) (Icc 0 E) η)
    (hp0 : p 0 = 0) (hpos : ∀ η ∈ Ico 0 E, 0 < q η) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Ico 0 (p E), ψ t ∈ Ico 0 E ∧ p (ψ t) = t) ∧
      (∀ η ∈ Ico 0 E, ψ (p η) = η) ∧
      ContinuousOn (fun t => q (ψ t)) (Ico 0 (p E)) ∧
      ContinuousOn (fun t => f (ψ t)) (Ico 0 (p E)) ∧
      (∀ t ∈ Ioo 0 (p E), HasDerivAt (fun s => f (ψ s)) (t / q (ψ t)) t) ∧
      (∀ t ∈ Ioo 0 (p E), HasDerivAt (fun s => q (ψ s)) (-(k * f (ψ t)) + (1 - t ^ 2) / q (ψ t)) t) ∧
      ContinuousOn ψ (Ico 0 (p E)) ∧
      (∀ t ∈ Ioo 0 (p E), HasDerivAt ψ (q (ψ t))⁻¹ t) := by
  have hfc : ContinuousOn f (Icc 0 E) := fun x hx => (hf x hx).continuousWithinAt
  have hpc : ContinuousOn p (Icc 0 E) := fun x hx => (hp x hx).continuousWithinAt
  have hqc : ContinuousOn q (Icc 0 E) := fun x hx => (hq x hx).continuousWithinAt
  -- interior derivatives
  have hpA : ∀ x ∈ Ioo 0 E, HasDerivAt p (q x) x := fun x hx =>
    (hp x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hfA : ∀ x ∈ Ioo 0 E, HasDerivAt f (p x) x := fun x hx =>
    (hf x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hqA : ∀ x ∈ Ioo 0 E, HasDerivAt q (-(k * f x * q x) + 1 - p x ^ 2) x := fun x hx =>
    (hq x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hmono : StrictMonoOn p (Icc 0 E) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 E) hpc
    intro x hx
    rw [interior_Icc] at hx
    rw [(hpA x hx).deriv]
    exact hpos x ⟨hx.1.le, hx.2⟩
  have hE0 : (0 : ℝ) ≤ E := hE.le
  have hpE : 0 < p E := by
    have := hmono ⟨le_rfl, hE0⟩ ⟨hE0, le_rfl⟩ hE
    rwa [hp0] at this
  have hsurj : ∀ t ∈ Icc 0 (p E), ∃ η ∈ Icc 0 E, p η = t := by
    intro t ht
    rw [← hp0] at ht
    exact intermediate_value_Icc hE0 hpc ht
  set ψ := Function.invFunOn p (Icc 0 E) with hψdef
  have hψ : ∀ t ∈ Icc 0 (p E), ψ t ∈ Icc 0 E ∧ p (ψ t) = t := fun t ht =>
    Function.invFunOn_pos (hsurj t ht)
  have hψp : ∀ η ∈ Icc 0 E, ψ (p η) = η := fun η hη =>
    hmono.injOn.leftInvOn_invFunOn hη
  have hψ' : ∀ t ∈ Ico 0 (p E), ψ t ∈ Ico 0 E ∧ p (ψ t) = t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hψ t (Ico_subset_Icc_self ht)
    refine ⟨⟨h1.1, lt_of_le_of_ne h1.2 ?_⟩, h2⟩
    intro h
    rw [h] at h2
    exact absurd h2 (ne_of_gt ht.2)
  have hψi : ∀ t ∈ Ioo 0 (p E), ψ t ∈ Ioo 0 E := by
    intro t ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := hψ' t (Ioo_subset_Ico_self ht)
    refine ⟨lt_of_le_of_ne h1 ?_, h2⟩
    intro h
    rw [← h, hp0] at h3
    exact absurd h3 (ne_of_lt ht.1)
  have hψmono : MonotoneOn ψ (Icc 0 (p E)) := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := hψ a ha
    obtain ⟨hb1, hb2⟩ := hψ b hb
    rw [← hmono.le_iff_le ha1 hb1, ha2, hb2]
    exact hab
  have himg : Icc 0 E ⊆ ψ '' Icc 0 (p E) := by
    intro η hη
    refine ⟨p η, ⟨?_, ?_⟩, hψp η hη⟩
    · rw [← hp0]; exact hmono.monotoneOn ⟨le_rfl, hE0⟩ hη hη.1
    · exact hmono.monotoneOn hη ⟨hE0, le_rfl⟩ hη.2
  have hψ0 : ψ 0 = 0 := by
    have := hψp 0 ⟨le_rfl, hE0⟩
    rwa [hp0] at this
  have hψcA : ∀ t ∈ Ioo 0 (p E), ContinuousAt ψ t := by
    intro t ht
    have hi := hψi t ht
    apply continuousAt_of_monotoneOn_of_image_mem_nhds hψmono
      (Icc_mem_nhds ht.1 ht.2)
    exact Filter.mem_of_superset (Icc_mem_nhds hi.1 hi.2) himg
  have hψc : ContinuousOn ψ (Ico 0 (p E)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      have : ContinuousWithinAt ψ (Ici 0) 0 := by
        apply continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin hψmono
          (Icc_mem_nhdsGE hpE)
        rw [hψ0]
        exact Filter.mem_of_superset (Icc_mem_nhdsGE hE) himg
      exact this.mono Ico_subset_Ici_self
    · exact (hψcA t ⟨h, ht.2⟩).continuousWithinAt
  have hmaps : MapsTo ψ (Ico 0 (p E)) (Icc 0 E) := fun t ht =>
    Ico_subset_Icc_self (hψ' t ht).1
  have hψD : ∀ t ∈ Ioo 0 (p E), HasDerivAt ψ (q (ψ t))⁻¹ t := by
    intro t ht
    have hi := hψi t ht
    apply HasDerivAt.of_local_left_inverse (hψcA t ht) (hpA _ hi)
      (hpos _ (Ioo_subset_Ico_self hi)).ne'
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact (hψ' y (Ioo_subset_Ico_self hy)).2
  refine ⟨ψ, hψ', fun η hη => hψp η (Ico_subset_Icc_self hη),
    hqc.comp hψc hmaps, hfc.comp hψc hmaps, ?_, ?_, hψc, hψD⟩
  · intro t ht
    have hi := hψi t ht
    have hqne := (hpos _ (Ioo_subset_Ico_self hi)).ne'
    have := (hfA _ hi).comp t (hψD t ht)
    refine this.congr_deriv ?_
    rw [(hψ' t (Ioo_subset_Ico_self ht)).2]
    field_simp
  · intro t ht
    have hi := hψi t ht
    have hqne := (hpos _ (Ioo_subset_Ico_self hi)).ne'
    have := (hqA _ hi).comp t (hψD t ht)
    refine this.congr_deriv ?_
    rw [(hψ' t (Ioo_subset_Ico_self ht)).2]
    field_simp
    ring

end Work.FalknerSkan.NegCrocco
