import Work.FalknerSkan.CroccoCompare
import Work.FalknerSkan.CroccoMap

/-!
# Crocco variables: the wall shear of a monotone solution between two shooting values

Run 2026-11-08T1028Z, helper for `Work.FalknerSkan.MonotoneWindow`, generic in the coefficient
k ≥ 0 of f''' + k f f'' + 1 − f'² = 0 (k = 1 Hiemenz, k = 2 Homann). A boundary-value solution
(f(0) = f'(0) = 0, f' → 1) with f'' > 0 on [0, ∞) is compared, in Crocco variables, with a
solution of the initial-value problem that overshoots (`le_of_over`: its wall shear is not
smaller) or undershoots (`ge_of_under`: not larger).
-/

namespace Work.FalknerSkan.CroccoWindow
open Set Filter Topology

/-- A function with positive derivative within [0, E] on [0, E) is strictly increasing there. -/
theorem smono_Icc {E : ℝ} {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Icc 0 E, HasDerivWithinAt p (q η) (Icc 0 E) η)
    (hpos : ∀ η ∈ Ico 0 E, 0 < q η) : StrictMonoOn p (Icc 0 E) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 E)
  · intro x hx; exact (hp x hx).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hp x ⟨hx.1.le, hx.2.le⟩).mono interior_subset
  · intro x hx
    rw [interior_Icc] at hx
    exact hpos x ⟨hx.1.le, hx.2⟩

/-- Same on [0, ∞). -/
theorem smono_Ici {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) : StrictMonoOn p (Ici 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
  · intro x hx; exact (hp x hx).continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hp x (Set.mem_Ici.2 (le_of_lt hx))).mono interior_subset
  · intro x hx
    rw [interior_Ici] at hx
    exact hpos x (Set.mem_Ici.2 (le_of_lt hx))

/-- A boundary-value solution with f'' > 0 has f' < 1 everywhere. -/
theorem p_lt_one {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hlim : Tendsto p atTop (𝓝 1)) (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    ∀ η ∈ Ici (0 : ℝ), p η < 1 := by
  have hm := smono_Ici hp hpos
  intro η hη
  have hη0 : (0 : ℝ) ≤ η := hη
  have h1 : p η < p (η + 1) := hm hη (show (0 : ℝ) ≤ η + 1 by linarith) (by linarith)
  have h2 : p (η + 1) ≤ 1 := by
    apply ge_of_tendsto hlim
    rw [eventually_atTop]
    refine ⟨η + 1, fun s hs => ?_⟩
    exact hm.monotoneOn (show (0 : ℝ) ≤ η + 1 by linarith) (show (0 : ℝ) ≤ s by linarith) hs
  linarith

/-- A boundary-value solution with f'' > 0 has f'' below any ε > 0 somewhere. -/
theorem exists_q_lt {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) (hp0 : p 0 = 0)
    (hlim : Tendsto p atTop (𝓝 1)) (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    {ε : ℝ} (hε : 0 < ε) : ∃ η ∈ Ici (0 : ℝ), q η < ε := by
  by_contra hcon
  push_neg at hcon
  have hmono : MonotoneOn (fun x => p x - ε * x) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => q x - ε) (convex_Ici 0)
    · intro x hx
      exact ((hp x hx).continuousWithinAt).sub (continuousWithinAt_id.const_mul ε)
    · intro x hx
      rw [interior_Ici] at hx
      have h := (hp x (Set.mem_Ici.2 (le_of_lt hx))).sub ((hasDerivWithinAt_id x (Ici 0)).const_mul ε)
      have h' := h.mono (interior_subset (s := Ici (0 : ℝ)))
      rw [interior_Ici] at h'
      rw [interior_Ici]; exact h'.congr_deriv (by ring)
    · intro x hx
      rw [interior_Ici] at hx
      have := hcon x (Set.mem_Ici.2 (le_of_lt hx))
      linarith
  have hx : (0 : ℝ) ≤ 2 / ε := by positivity
  have h1 := hmono (Set.mem_Ici.2 le_rfl) hx hx
  simp only [hp0, mul_zero, sub_zero] at h1
  have h2 : ε * (2 / ε) = 2 := by field_simp
  have h3 := p_lt_one hp hlim hpos (2 / ε) hx
  linarith

/-- Comparison with an overshooting solution of the initial-value problem: the boundary-value
solution's wall shear is at most the overshooting one's. -/
theorem le_of_over {k S α : ℝ} (hk : 0 ≤ k) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    {g u v : ℝ → ℝ}
    (hg : ∀ η ∈ Icc 0 S, HasDerivWithinAt g (u η) (Icc 0 S) η)
    (hu : ∀ η ∈ Icc 0 S, HasDerivWithinAt u (v η) (Icc 0 S) η)
    (hv : ∀ η ∈ Icc 0 S, HasDerivWithinAt v (-(k * g η * v η) - 1 + u η ^ 2) (Icc 0 S) η)
    (hg0 : g 0 = 0) (hu0 : u 0 = 0) (hv0 : v 0 = α)
    (hover : ∃ η ∈ Ioc 0 S, 1 < u η ∧ ∀ s ∈ Icc 0 η, 0 < v s) : q 0 ≤ α := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨η0, ⟨h0pos, h0S⟩, hu1, hvpos⟩ := hover
  have hsub : Icc 0 η0 ⊆ Icc 0 S := Icc_subset_Icc le_rfl h0S
  obtain ⟨ψ1, hψ1a, hψ1b, cz1, cF1, dF1, dz1⟩ := Work.FalknerSkan.CroccoMap.crocco (k := k) h0pos
    (fun η hη => (hg η (hsub hη)).mono hsub) (fun η hη => (hu η (hsub hη)).mono hsub)
    (fun η hη => (hv η (hsub hη)).mono hsub) hu0 (fun η hη => hvpos η ⟨hη.1, hη.2.le⟩)
  have hD0 : 0 < q 0 - α := by linarith
  obtain ⟨ηs, hηs, hqs⟩ := exists_q_lt hp hp0 hlim hpos hD0
  have hηs0 : (0 : ℝ) ≤ ηs := hηs
  set E := ηs + 1 with hE
  have hE0 : 0 < E := by linarith
  have hsubE : Icc 0 E ⊆ Ici 0 := fun x hx => hx.1
  obtain ⟨ψ2, hψ2a, hψ2b, cz2, cF2, dF2, dz2⟩ := Work.FalknerSkan.CroccoMap.crocco (k := k) hE0
    (fun η hη => (hf η (hsubE hη)).mono hsubE) (fun η hη => (hp η (hsubE hη)).mono hsubE)
    (fun η hη => (hq η (hsubE hη)).mono hsubE) hp0 (fun η hη => hpos η hη.1)
  have hm := smono_Ici hp hpos
  have hpE1 : p E < 1 := p_lt_one hp hlim hpos E hE0.le
  have hLu : p E ≤ u η0 := by linarith
  have hsub1 : Ico 0 (p E) ⊆ Ico 0 (u η0) := Ico_subset_Ico_right hLu
  have hsub1' : Ioo 0 (p E) ⊆ Ioo 0 (u η0) := Ioo_subset_Ioo_right hLu
  have hψ10 : ψ1 0 = 0 := by
    have := hψ1b 0 ⟨le_rfl, h0pos⟩; rwa [hu0] at this
  have hψ20 : ψ2 0 = 0 := by
    have := hψ2b 0 ⟨le_rfl, hE0⟩; rwa [hp0] at this
  have hcmp := Work.FalknerSkan.CroccoCompare.compare (k := k) (L := p E)
    (z₁ := fun t => v (ψ1 t)) (z₂ := fun t => q (ψ2 t))
    (F₁ := fun t => g (ψ1 t)) (F₂ := fun t => f (ψ2 t)) hk hpE1.le
    (fun t ht => by
      obtain ⟨h1, -⟩ := hψ1a t (hsub1 ht)
      exact hvpos _ ⟨h1.1, h1.2.le⟩)
    (fun t ht => hpos _ (hψ2a t ht).1.1)
    (cz1.mono hsub1) cz2 (cF1.mono hsub1) cF2
    (fun t ht => dF1 t (hsub1' ht)) dF2 (fun t ht => dz1 t (hsub1' ht)) dz2
    (by simp only [hψ10, hψ20, hg0, hf0])
    (by simp only [hψ10, hψ20, hv0]; exact hlt)
  have hts : p ηs ∈ Ico 0 (p E) := by
    refine ⟨?_, hm hηs hE0.le (by linarith)⟩
    have := hm.monotoneOn (Set.mem_Ici.2 le_rfl) hηs hηs0
    rwa [hp0] at this
  have key := hcmp (p ηs) hts
  simp only [hψ10, hψ20, hv0] at key
  rw [hψ2b ηs ⟨hηs0, by linarith⟩] at key
  have hvp : 0 < v (ψ1 (p ηs)) := by
    obtain ⟨h1, -⟩ := hψ1a _ (hsub1 hts)
    exact hvpos _ ⟨h1.1, h1.2.le⟩
  linarith

/-- Comparison with an undershooting solution of the initial-value problem: the boundary-value
solution's wall shear is at least the undershooting one's. -/
theorem ge_of_under {k S α : ℝ} (hk : 0 ≤ k) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    {g u v : ℝ → ℝ}
    (hg : ∀ η ∈ Icc 0 S, HasDerivWithinAt g (u η) (Icc 0 S) η)
    (hu : ∀ η ∈ Icc 0 S, HasDerivWithinAt u (v η) (Icc 0 S) η)
    (hv : ∀ η ∈ Icc 0 S, HasDerivWithinAt v (-(k * g η * v η) - 1 + u η ^ 2) (Icc 0 S) η)
    (hg0 : g 0 = 0) (hu0 : u 0 = 0) (hv0 : v 0 = α)
    (hunder : ∃ η ∈ Ioc 0 S, v η < 0 ∧ ∀ s ∈ Icc 0 η, u s < 1) : α ≤ q 0 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨ηu, ⟨hu0pos, huS⟩, hvneg, hu1⟩ := hunder
  have hα : 0 < α := lt_trans (hpos 0 (Set.mem_Ici.2 le_rfl)) hlt
  -- the first zero η1 of v
  set Z := Icc 0 ηu ∩ v ⁻¹' Iic 0 with hZ
  have hsubu : Icc 0 ηu ⊆ Icc 0 S := Icc_subset_Icc le_rfl huS
  have cv : ContinuousOn v (Icc 0 ηu) := fun x hx => ((hv x (hsubu hx)).continuousWithinAt).mono hsubu
  have hZc : IsClosed Z := cv.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZne : Z.Nonempty := ⟨ηu, ⟨⟨hu0pos.le, le_rfl⟩, hvneg.le⟩⟩
  have hZbdd : BddBelow Z := ⟨0, fun x hx => hx.1.1⟩
  set η1 := sInf Z with hη1
  have hη1Z : η1 ∈ Z := hZc.csInf_mem hZne hZbdd
  have hv1 : v η1 ≤ 0 := hη1Z.2
  have hη1u : η1 ≤ ηu := hη1Z.1.2
  have hη1pos : 0 < η1 := by
    rcases (hη1Z.1.1).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hv1; linarith
  have hvpos : ∀ s ∈ Ico 0 η1, 0 < v s := by
    intro s hs
    by_contra hc
    push_neg at hc
    have : η1 ≤ s := csInf_le hZbdd ⟨⟨hs.1, by linarith [hs.2]⟩, hc⟩
    linarith [hs.2]
  have hsub : Icc 0 η1 ⊆ Icc 0 S := Icc_subset_Icc le_rfl (hη1u.trans huS)
  have hg' := fun η (hη : η ∈ Icc 0 η1) => (hg η (hsub hη)).mono hsub
  have hu' := fun η (hη : η ∈ Icc 0 η1) => (hu η (hsub hη)).mono hsub
  have hv' := fun η (hη : η ∈ Icc 0 η1) => (hv η (hsub hη)).mono hsub
  obtain ⟨ψ1, hψ1a, hψ1b, cz1, cF1, dF1, dz1⟩ :=
    Work.FalknerSkan.CroccoMap.crocco (k := k) hη1pos hg' hu' hv' hu0 hvpos
  have hum := smono_Icc hu' hvpos
  have hL1 : u η1 < 1 := hu1 η1 ⟨hη1pos.le, hη1u⟩
  -- a boundary-value horizon E with p E > u η1
  obtain ⟨E, hE1, hEu⟩ : ∃ E, 1 ≤ E ∧ u η1 < p E := by
    have h := (hlim.eventually (lt_mem_nhds hL1)).and (eventually_ge_atTop (1 : ℝ))
    obtain ⟨E, hE⟩ := h.exists
    exact ⟨E, hE.2, hE.1⟩
  have hE0 : 0 < E := by linarith
  have hsubE : Icc 0 E ⊆ Ici 0 := fun x hx => hx.1
  obtain ⟨ψ2, hψ2a, hψ2b, cz2, cF2, dF2, dz2⟩ := Work.FalknerSkan.CroccoMap.crocco (k := k) hE0
    (fun η hη => (hf η (hsubE hη)).mono hsubE) (fun η hη => (hp η (hsubE hη)).mono hsubE)
    (fun η hη => (hq η (hsubE hη)).mono hsubE) hp0 (fun η hη => hpos η hη.1)
  have hsub2 : Ico 0 (u η1) ⊆ Ico 0 (p E) := Ico_subset_Ico_right hEu.le
  have hsub2' : Ioo 0 (u η1) ⊆ Ioo 0 (p E) := Ioo_subset_Ioo_right hEu.le
  have hψ10 : ψ1 0 = 0 := by
    have := hψ1b 0 ⟨le_rfl, hη1pos⟩; rwa [hu0] at this
  have hψ20 : ψ2 0 = 0 := by
    have := hψ2b 0 ⟨le_rfl, hE0⟩; rwa [hp0] at this
  have hcmp := Work.FalknerSkan.CroccoCompare.compare (k := k) (L := u η1)
    (z₁ := fun t => q (ψ2 t)) (z₂ := fun t => v (ψ1 t))
    (F₁ := fun t => f (ψ2 t)) (F₂ := fun t => g (ψ1 t)) hk hL1.le
    (fun t ht => hpos _ (hψ2a t (hsub2 ht)).1.1)
    (fun t ht => hvpos _ (hψ1a t ht).1)
    (cz2.mono hsub2) cz1 (cF2.mono hsub2) cF1
    (fun t ht => dF2 t (hsub2' ht)) dF1 (fun t ht => dz2 t (hsub2' ht)) dz1
    (by simp only [hψ10, hψ20, hg0, hf0])
    (by simp only [hψ10, hψ20, hv0]; exact hlt)
  simp only [hψ10, hψ20, hv0] at hcmp
  -- v > α − q 0 on [0, η1)
  have hbig : ∀ s ∈ Ico 0 η1, α - q 0 < v s := by
    intro s hs
    have hts : u s ∈ Ico 0 (u η1) := by
      refine ⟨?_, hum ⟨hs.1, hs.2.le⟩ ⟨hη1pos.le, le_rfl⟩ hs.2⟩
      have := hum.monotoneOn ⟨le_rfl, hη1pos.le⟩ ⟨hs.1, hs.2.le⟩ hs.1
      rwa [hu0] at this
    have key := hcmp (u s) hts
    rw [hψ1b s hs] at key
    have hq2 : 0 < q (ψ2 (u s)) := hpos _ (hψ2a _ (hsub2 hts)).1.1
    linarith
  -- continuity of v at η1 from the left
  have hcont : ContinuousWithinAt v (Iio η1) η1 := by
    have h := (hv η1 ⟨hη1pos.le, hη1u.trans huS⟩).continuousWithinAt
    apply h.mono_of_mem_nhdsWithin
    filter_upwards [Ioo_mem_nhdsLT hη1pos] with x hx
    exact ⟨hx.1.le, (hx.2.le.trans hη1u).trans huS⟩
  have hge : α - q 0 ≤ v η1 := by
    apply ge_of_tendsto hcont
    filter_upwards [Ioo_mem_nhdsLT hη1pos] with x hx
    exact (hbig x ⟨hx.1.le, hx.2⟩).le
  linarith

end Work.FalknerSkan.CroccoWindow
