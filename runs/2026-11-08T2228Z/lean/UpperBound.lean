import Checked.FalknerSkan.Bounded
/-! Scratch (run 2026-11-08T2228Z, STATE exact next step 4): for the stagnation-point equations the upper half of
the class −1 ≤ f' ≤ 1 is automatic. At an interior maximum of p = f' above one, q = f'' vanishes and the equation
gives q' = p² − 1 > 0, so p increases just after: no maximum. Hence every solution with p(0) = 0 and p → 1 has
p ≤ 1, and the Hiemenz/Homann window and uniqueness theorems need only −1 ≤ f'. -/

namespace Scratch2228
open Set Filter Topology

/-- If p' = q and q' = g on [0, ∞) (one-sided at 0), p(0) ≤ 1, p → 1, and g > 0 wherever q = 0 and p > 1,
then p ≤ 1 on [0, ∞). -/
theorem le_one_of_tendsto {p q g : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (g η) (Ici 0) η)
    (hp0 : p 0 ≤ 1) (hlim : Tendsto p atTop (𝓝 1))
    (hg : ∀ η ∈ Ici (0 : ℝ), q η = 0 → 1 < p η → 0 < g η) :
    ∀ η ∈ Ici (0 : ℝ), p η ≤ 1 := by
  intro η₀ hη₀
  by_contra hcon
  have h1 : 1 < p η₀ := not_le.1 hcon
  have hnhds : ∀ t, 0 < t → Ici (0 : ℝ) ∈ 𝓝 t := fun t ht => Ici_mem_nhds ht
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds h1))
  set T' := max T η₀ with hT'
  have hcont : ContinuousOn p (Icc 0 T') := fun x hx =>
    ((hp x hx.1).continuousWithinAt).mono (fun y hy => hy.1)
  obtain ⟨η₁, hη₁, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 ((show (0 : ℝ) ≤ η₀ from hη₀).trans (le_max_right _ _))) hcont
  have hge : p η₀ ≤ p η₁ := hmax ⟨hη₀, le_max_right _ _⟩
  have hglob : ∀ η, 0 ≤ η → p η ≤ p η₁ := by
    intro η hη
    rcases le_or_gt η T' with h | h
    · exact hmax ⟨hη, h⟩
    · exact ((hT η ((le_max_left _ _).trans h.le))).le.trans hge
  have hpos : 0 < η₁ := by
    rcases eq_or_lt_of_le hη₁.1 with h | h
    · rw [← h] at hge; linarith
    · exact h
  have hpd : HasDerivAt p (q η₁) η₁ := (hp η₁ hη₁.1).hasDerivAt (hnhds η₁ hpos)
  have hq0 : q η₁ = 0 := by
    have hlm : IsLocalMax p η₁ := by
      filter_upwards [hnhds η₁ hpos] with y hy
      exact hglob y hy
    exact hlm.hasDerivAt_eq_zero hpd
  have hgpos : 0 < g η₁ := hg η₁ hη₁.1 hq0 (lt_of_lt_of_le h1 hge)
  have hqd : HasDerivAt q (g η₁) η₁ := (hq η₁ hη₁.1).hasDerivAt (hnhds η₁ hpos)
  -- q > 0 just to the right of η₁
  have hslope := hqd.tendsto_slope
  have hev : ∀ᶠ η in 𝓝[>] η₁, 0 < q η := by
    have h2 : ∀ᶠ η in 𝓝[≠] η₁, 0 < slope q η₁ η := hslope.eventually (lt_mem_nhds hgpos)
    have h3 : ∀ᶠ η in 𝓝[>] η₁, 0 < slope q η₁ η :=
      nhdsWithin_mono _ (fun y hy => ne_of_gt hy) h2
    filter_upwards [h3, self_mem_nhdsWithin] with η hs hη
    rw [slope_def_field, hq0, sub_zero] at hs
    have hd : 0 < η - η₁ := sub_pos.2 hη
    exact (div_pos_iff_of_pos_right hd).1 hs
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu' : η₁ < u := hu
  set η₂ := (η₁ + u) / 2 with hη₂
  have h12 : η₁ < η₂ := by rw [hη₂]; linarith
  have h2u : η₂ < u := by rw [hη₂]; linarith
  have hcont2 : ContinuousOn p (Icc η₁ η₂) := fun x hx =>
    ((hp x (hη₁.1.trans hx.1)).continuousWithinAt).mono (fun y hy => hη₁.1.trans hy.1)
  have hder2 : ∀ x ∈ Ioo η₁ η₂, HasDerivAt p (q x) x := fun x hx =>
    (hp x (hpos.le.trans hx.1.le)).hasDerivAt (hnhds x (hpos.trans hx.1))
  obtain ⟨c, hc, hcq⟩ := exists_hasDerivAt_eq_slope p q h12 hcont2 hder2
  have hqc : 0 < q c := hsub ⟨hc.1, hc.2.trans h2u⟩
  rw [hcq] at hqc
  have : p η₁ < p η₂ := by
    have hd : 0 < η₂ - η₁ := sub_pos.2 h12
    have := (div_pos_iff_of_pos_right hd).1 hqc
    linarith
  exact absurd (hglob η₂ (hη₁.1.trans h12.le)) (not_le.2 this)

/-- The stagnation-point system (any real k): p ≤ 1 on [0, ∞) for every solution with p(0) = 0 and p → 1. -/
theorem fs_le_one {k : ℝ} {f p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) : ∀ η ∈ Ici (0 : ℝ), p η ≤ 1 :=
  le_one_of_tendsto hp hq (by rw [hp0]; norm_num) hlim (fun η _ hq0 hp1 => by
    rw [hq0]; nlinarith)

/-- Hiemenz: the window theorem with only −1 ≤ f' (the upper bound f' ≤ 1 is automatic). -/
theorem hiemenz_lower_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 1 + p η ^ 2) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  exact Checked.FalknerSkan.Bounded.hiemenz_bounded_window f p q hf hp hq hf0 hp0 hlim
    (fun η hη => ⟨hb η hη, fs_le_one hp hq1 hp0 hlim η hη⟩)

/-- Homann: the window theorem with only −1 ≤ f'. -/
theorem homann_lower_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η) :
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 :=
  Checked.FalknerSkan.Bounded.homann_bounded_window f p q hf hp hq hf0 hp0 hlim
    (fun η hη => ⟨hb η hη, fs_le_one hp hq hp0 hlim η hη⟩)

end Scratch2228

#print axioms Scratch2228.hiemenz_lower_window
#print axioms Scratch2228.homann_lower_window
