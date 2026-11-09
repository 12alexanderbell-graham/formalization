import Checked.FalknerSkan.BoundedTools
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
/-! Stagnation-point equations f' = p, p' = q, q' = −K f q − 1 + p² with K ≥ 1: every solution on the
closed half-line with f(0) = 0, p(0) = 0 and p → 1 has q > 0 everywhere, so no bound on p is needed
in the window and uniqueness theorems. Proof: runs/2026-11-09T0028Z/coppel/REPORT.md (lemmas L0–L8;
L3 is `touch`, by backward uniqueness). Run 2026-11-09T0028Z. -/

namespace Work.FalknerSkan.UnrestrictedCore
open Set Filter Topology

/-! ### Calculus tools on the closed half-line -/

theorem cont_of {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a b : ℝ} (ha : 0 ≤ a) : ContinuousOn g (Icc a b) := fun x hx =>
  ((hg x (ha.trans hx.1)).continuousWithinAt).mono (fun _ hy => ha.trans hy.1)

theorem at_of {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {x : ℝ} (hx : 0 < x) : HasDerivAt g (g' x) x :=
  (hg x hx.le).hasDerivAt (Ici_mem_nhds hx)

theorem int_of {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a b : ℝ} (ha : 0 ≤ a) :
    ∀ x ∈ interior (Icc a b), HasDerivWithinAt g (g' x) (interior (Icc a b)) x := by
  intro x hx
  rw [interior_Icc] at hx
  exact (at_of hg (ha.trans_lt hx.1)).hasDerivWithinAt

theorem smono {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a b : ℝ} (ha : 0 ≤ a) (h : ∀ x ∈ Ioo a b, 0 < g' x) : StrictMonoOn g (Icc a b) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) (cont_of hg ha) (int_of hg ha)
    (fun x hx => h x (by rwa [interior_Icc] at hx))

theorem santi {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a b : ℝ} (ha : 0 ≤ a) (h : ∀ x ∈ Ioo a b, g' x < 0) : StrictAntiOn g (Icc a b) :=
  strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b) (cont_of hg ha) (int_of hg ha)
    (fun x hx => h x (by rwa [interior_Icc] at hx))

theorem mono {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a b : ℝ} (ha : 0 ≤ a) (h : ∀ x ∈ Ioo a b, 0 ≤ g' x) : MonotoneOn g (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (cont_of hg ha) (int_of hg ha)
    (fun x hx => h x (by rwa [interior_Icc] at hx))

theorem anti {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a b : ℝ} (ha : 0 ≤ a) (h : ∀ x ∈ Ioo a b, g' x ≤ 0) : AntitoneOn g (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (cont_of hg ha) (int_of hg ha)
    (fun x hx => h x (by rwa [interior_Icc] at hx))

/-- A right derivative at a point after which the function does not go below its value is ≥ 0. -/
theorem right_nonneg {g : ℝ → ℝ} {d x : ℝ} (h : HasDerivWithinAt g d (Ici x) x)
    (hev : ∀ᶠ y in 𝓝[>] x, g x ≤ g y) : 0 ≤ d := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 (h.mono Ioi_subset_Ici_self)
  rw [sdiff_singleton_eq_self (by simp)] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hy'
  have hy'' : x < y := hy'
  rw [slope_def_field]
  exact div_nonneg (by linarith) (by linarith)

/-- A right derivative at a point after which the function does not go above its value is ≤ 0. -/
theorem right_nonpos {g : ℝ → ℝ} {d x : ℝ} (h : HasDerivWithinAt g d (Ici x) x)
    (hev : ∀ᶠ y in 𝓝[>] x, g y ≤ g x) : d ≤ 0 := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 (h.mono Ioi_subset_Ici_self)
  rw [sdiff_singleton_eq_self (by simp)] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hy'
  have hy'' : x < y := hy'
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- A positive derivative at a zero: the function is negative just to the left. -/
theorem left_neg {g : ℝ → ℝ} {d x : ℝ} (h : HasDerivAt g d x) (hd : 0 < d) (h0 : g x = 0) :
    ∀ᶠ y in 𝓝[<] x, g y < 0 := by
  have ht := hasDerivAt_iff_tendsto_slope.1 h
  have hs : ∀ᶠ y in 𝓝[<] x, 0 < slope g x y :=
    (ht.mono_left (nhdsWithin_mono _ (fun y hy => ne_of_lt hy))).eventually (lt_mem_nhds hd)
  filter_upwards [hs, self_mem_nhdsWithin] with y hy hy'
  have hlt : y - x < 0 := sub_neg.2 hy'
  rw [slope_def_field, h0, sub_zero] at hy
  rcases div_pos_iff.1 hy with ⟨_, h2⟩ | ⟨h1, _⟩
  · linarith
  · exact h1

theorem le_of_right {g : ℝ → ℝ} {x c : ℝ} (h : ContinuousWithinAt g (Ici x) x)
    (hev : ∀ᶠ y in 𝓝[>] x, g y ≤ c) : g x ≤ c :=
  le_of_tendsto (h.mono Ioi_subset_Ici_self).tendsto hev

theorem ge_of_right {g : ℝ → ℝ} {x c : ℝ} (h : ContinuousWithinAt g (Ici x) x)
    (hev : ∀ᶠ y in 𝓝[>] x, c ≤ g y) : c ≤ g x :=
  ge_of_tendsto (h.mono Ioi_subset_Ici_self).tendsto hev

/-- L0: a positive weight W with W' = a f W on the closed half-line. -/
theorem weight {f p : ℝ → ℝ} (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) (a : ℝ) :
    ∃ W : ℝ → ℝ, (∀ η, 0 < W η) ∧
      ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt W (a * f η * W η) (Ici 0) η := by
  have hfc : ContinuousOn f (Ici 0) := fun x hx => (hf x hx).continuousWithinAt
  set g : ℝ → ℝ := fun x => f (max x 0) with hgdef
  have hg : Continuous g :=
    hfc.comp_continuous (continuous_id.max continuous_const) (fun x => le_max_right x 0)
  refine ⟨fun u => Real.exp (a * ∫ x in (0 : ℝ)..u, g x), fun η => Real.exp_pos _, ?_⟩
  intro η hη
  have hη0 : (0 : ℝ) ≤ η := hη
  have h1 := (((hg.integral_hasStrictDerivAt 0 η).hasDerivAt).const_mul a).exp
  have hgη : g η = f η := by simp [hgdef, max_eq_left hη0]
  rw [hgη] at h1
  exact h1.hasDerivWithinAt.congr_deriv (by ring)

/-- Interior maximum: zero derivative. -/
theorem q_zero_of_max {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    {η₁ : ℝ} (hη₁ : 0 < η₁) (hmax : ∀ η ∈ Ici (0 : ℝ), p η ≤ p η₁) : q η₁ = 0 := by
  have hlm : IsLocalMax p η₁ := by
    filter_upwards [Ici_mem_nhds hη₁] with y hy
    exact hmax y hy
  exact hlm.hasDerivAt_eq_zero (at_of hp hη₁)


/-! ### The system f' = p, p' = q, q' = −K f q − 1 + p² -/

/-- Lemma (a): p ≤ 1 for every solution with p(0) ≤ 1, p → 1 (any K). -/
theorem le_one {K : ℝ} {f p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hp0 : p 0 ≤ 1) (hlim : Tendsto p atTop (𝓝 1)) : ∀ η ∈ Ici (0 : ℝ), p η ≤ 1 := by
  intro η₀ hη₀
  by_contra hcon
  have h1 : 1 < p η₀ := not_le.1 hcon
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds h1))
  set T' := max T η₀ with hT'
  obtain ⟨η₁, hη₁, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T')).exists_isMaxOn
    (nonempty_Icc.2 ((show (0 : ℝ) ≤ η₀ from hη₀).trans (le_max_right T η₀))) (cont_of hp le_rfl)
  have hge : p η₀ ≤ p η₁ := hmax ⟨hη₀, le_max_right T η₀⟩
  have hglob : ∀ η ∈ Ici (0 : ℝ), p η ≤ p η₁ := by
    intro η hη
    rcases le_or_gt η T' with h | h
    · exact hmax ⟨hη, h⟩
    · exact ((hT η ((le_max_left _ _).trans h.le))).le.trans hge
  have hpos : 0 < η₁ := by
    rcases eq_or_lt_of_le hη₁.1 with h | h
    · rw [← h] at hge; linarith
    · exact h
  have hq0 : q η₁ = 0 := q_zero_of_max hp hpos hglob
  have hgpos : 0 < -(K * f η₁ * q η₁) - 1 + p η₁ ^ 2 := by
    rw [hq0]; nlinarith
  -- q > 0 just to the right of η₁: use the right derivative
  have hslope := hasDerivWithinAt_iff_tendsto_slope.1
    (((at_of hq hpos).hasDerivWithinAt (s := Ioi η₁)))
  rw [sdiff_singleton_eq_self (by simp)] at hslope
  have h3 : ∀ᶠ y in 𝓝[>] η₁, 0 < slope q η₁ y := hslope.eventually (lt_mem_nhds hgpos)
  have hev2 : ∀ᶠ y in 𝓝[>] η₁, 0 < q y := by
    filter_upwards [h3, self_mem_nhdsWithin] with y hs hy
    have hy' : η₁ < y := hy
    rw [slope_def_field, hq0, sub_zero] at hs
    exact (div_pos_iff_of_pos_right (sub_pos.2 hy')).1 hs
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev2
  have hu' : η₁ < u := hu
  have hsm := smono hp hη₁.1 (b := (η₁ + u) / 2) (fun x hx => hsub ⟨hx.1, by linarith [hx.2]⟩)
  have := hsm ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  exact absurd (hglob _ (show (0 : ℝ) ≤ (η₁ + u) / 2 by linarith [hη₁.1])) (not_le.2 this)

/-- The derivative of r = −K f q − 1 + p². -/
theorem rder {K : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun y => -(K * f y * q y) - 1 + p y ^ 2)
      (-(K * f η * (-(K * f η * q η) - 1 + p η ^ 2)) - (K - 2) * p η * q η) (Ici 0) η := by
  intro η hη
  have h := ((((hf η hη).const_mul K).mul (hq η hη)).neg.sub_const 1).add ((hp η hη).pow 2)
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- L4: q is eventually positive. -/
theorem q_eventually_pos {K : ℝ} {f p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hlim : Tendsto p atTop (𝓝 1)) (hlt1 : ∀ η ∈ Ici (0 : ℝ), p η < 1) :
    ∃ T, 0 ≤ T ∧ ∀ η, T ≤ η → 0 < q η := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (show (-1 : ℝ) < 1 by norm_num)))
  refine ⟨max T 0, le_max_right _ _, fun η' hη' => ?_⟩
  by_contra hcon
  have hle0 : q η' ≤ 0 := not_lt.1 hcon
  have h0 : 0 ≤ η' := (le_max_right _ _).trans hη'
  have hneg : ∀ η, η' ≤ η → q η ≤ 0 := by
    intro η hη
    have hcont : ContinuousOn q (Icc η' η) := cont_of hq h0
    have hder : ∀ x ∈ Ico η' η, HasDerivWithinAt q (-(K * f x * q x) - 1 + p x ^ 2) (Ici x) x :=
      fun x hx => (hq x (h0.trans hx.1)).mono (fun y hy => h0.trans (hx.1.trans hy))
    have := image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => (0 : ℝ))
      (B' := fun _ => (0 : ℝ)) hcont hder hle0 continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _)
      (fun x hx hqx => by
        have h1 : -1 < p x := hT x ((le_max_left _ _).trans (hη'.trans hx.1))
        have h2 : p x < 1 := hlt1 x (h0.trans hx.1)
        rw [hqx]; nlinarith)
    exact this ⟨hη, le_rfl⟩
  have hanti : ∀ η, η' ≤ η → p η ≤ p η' := fun η hη =>
    anti hp h0 (fun x hx => hneg x hx.1.le) ⟨le_rfl, hη⟩ ⟨hη, le_rfl⟩ hη
  have hev : ∀ᶠ η in atTop, p η' < p η := hlim.eventually (lt_mem_nhds (hlt1 η' h0))
  obtain ⟨η, hη⟩ := (hev.and (eventually_ge_atTop η')).exists
  exact absurd (hanti η hη.2) (not_le.2 hη.1)

/-- L5: the last zero of q. -/
theorem last_zero {K : ℝ} {f p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) (hlt1 : ∀ η ∈ Ici (0 : ℝ), p η < 1)
    (htouch : ∀ η ∈ Ici (0 : ℝ), q η = 0 → p η ≠ -1)
    {η₁ : ℝ} (h₁ : 0 ≤ η₁) (hq₁ : q η₁ ≤ 0) :
    ∃ η₂ c, 0 < η₂ ∧ 0 ≤ c ∧ c < η₂ ∧ q η₂ = 0 ∧ p η₂ < -1 ∧ (∀ y, η₂ < y → 0 < q y) ∧
      (∀ y, c ≤ y → y < η₂ → q y < 0) := by
  obtain ⟨T, hT0, hT⟩ := q_eventually_pos hp hq hlim hlt1
  have hη₁T : η₁ < T := by
    by_contra h
    exact absurd (hT η₁ (not_lt.1 h)) (not_lt.2 hq₁)
  set S := Icc 0 T ∩ q ⁻¹' Iic 0 with hS
  have hScl : IsClosed S := (cont_of hq le_rfl).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  have hS1 : η₁ ∈ S := ⟨⟨h₁, hη₁T.le⟩, hq₁⟩
  set η₂ := sSup S with hη₂def
  have hmem : η₂ ∈ S := hSc.sSup_mem ⟨η₁, hS1⟩
  have hafter : ∀ y, η₂ < y → 0 < q y := by
    intro y hy
    by_contra hc
    push Not at hc
    rcases le_or_gt y T with hyT | hyT
    · have : y ∈ S := ⟨⟨hmem.1.1.trans hy.le, hyT⟩, hc⟩
      exact absurd (le_csSup hSc.bddAbove this) (not_le.2 hy)
    · exact absurd (hT y hyT.le) (not_lt.2 hc)
  have hη₂0 : 0 ≤ η₂ := hmem.1.1
  have hq2le : q η₂ ≤ 0 := hmem.2
  have hqd : HasDerivWithinAt q (-(K * f η₂ * q η₂) - 1 + p η₂ ^ 2) (Ici η₂) η₂ :=
    (hq η₂ hη₂0).mono (Ici_subset_Ici.2 hη₂0)
  have hq2ge : 0 ≤ q η₂ := ge_of_right hqd.continuousWithinAt
    (by filter_upwards [self_mem_nhdsWithin] with y hy; exact (hafter y hy).le)
  have hq2 : q η₂ = 0 := le_antisymm hq2le hq2ge
  have hr2 : 0 ≤ -(K * f η₂ * q η₂) - 1 + p η₂ ^ 2 := right_nonneg hqd
    (by filter_upwards [self_mem_nhdsWithin] with y hy; rw [hq2]; exact (hafter y hy).le)
  rw [hq2] at hr2
  have hp2 : p η₂ < -1 := by
    have hnm1 := htouch η₂ hη₂0 hq2
    have h2 := hlt1 η₂ hη₂0
    by_contra hc
    push Not at hc
    have h1 : -1 < p η₂ := lt_of_le_of_ne hc (Ne.symm hnm1)
    nlinarith
  have hη₂pos : 0 < η₂ := by
    rcases eq_or_lt_of_le hη₂0 with h | h
    · exfalso; rw [← h, hp0] at hp2; norm_num at hp2
    · exact h
  have hev := left_neg (at_of hq hη₂pos) (by rw [hq2]; nlinarith) hq2
  obtain ⟨a, ha, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have ha' : a < η₂ := ha
  refine ⟨η₂, max ((a + η₂) / 2) (η₂ / 2), hη₂pos, le_max_of_le_right (by linarith),
    max_lt (by linarith) (by linarith), hq2, hp2, hafter, fun y hy1 hy2 => hsub ⟨?_, hy2⟩⟩
  have := le_max_left ((a + η₂) / 2) (η₂ / 2)
  linarith

/-- L1 (ii): Φ = W (f r − p q) with W' = K f W has Φ' = −W q (q + 2(K − 1) f p). -/
theorem phider {K : ℝ} {f p q W : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hW : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt W (K * f η * W η) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun y => W y * (f y * (-(K * f y * q y) - 1 + p y ^ 2) - p y * q y))
      (-(W η * q η * (q η + 2 * (K - 1) * f η * p η))) (Ici 0) η := by
  intro η hη
  have h := (hW η hη).mul (((hf η hη).mul (rder hf hp hq η hη)).sub ((hp η hη).mul (hq η hη)))
  exact h.congr_deriv (by simp only [Pi.mul_apply, Pi.sub_apply]; ring)

/-- L1 (i): (W r)' = (2 − K) W p q. -/
theorem wrder {K : ℝ} {f p q W : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hW : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt W (K * f η * W η) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun y => W y * (-(K * f y * q y) - 1 + p y ^ 2))
      ((2 - K) * W η * p η * q η) (Ici 0) η := by
  intro η hη
  exact ((hW η hη).mul (rder hf hp hq η hη)).congr_deriv (by ring)

/-- L1 (iii): Ω = M (p² − 1 − 2 f q) with M' = 2 f M has Ω' = 2(K − 2) M f² q. -/
theorem omder {K : ℝ} {f p q M : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hM : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt M (2 * f η * M η) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun y => M y * (p y ^ 2 - 1 - 2 * f y * q y))
      (2 * (K - 2) * M η * f η ^ 2 * q η) (Ici 0) η := by
  intro η hη
  have h := (hM η hη).mul ((((hp η hη).pow 2).sub_const 1).sub
    (((hf η hη).const_mul 2).mul (hq η hη)))
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- L7 (Ascent, 1 ≤ K ≤ 2). -/
theorem ascent {K : ℝ} (hK1 : 1 ≤ K) (hK2 : K ≤ 2) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hlim : Tendsto p atTop (𝓝 1)) (hle1 : ∀ η ∈ Ici (0 : ℝ), p η ≤ 1)
    {η₂ : ℝ} (h0 : 0 ≤ η₂) (hq2 : q η₂ = 0) (hp2 : p η₂ ≤ -1) (hf2 : f η₂ ≤ 0)
    (hafter : ∀ y, η₂ < y → 0 < q y) : False := by
  obtain ⟨W, hWpos, hW⟩ := weight hf K
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  have hsm : ∀ B, StrictMonoOn p (Icc η₂ B) := fun B => smono hp h0 (fun x hx => hafter x hx.1)
  set b := max T (η₂ + 1) with hb
  have hb2 : η₂ < b := by have := le_max_right T (η₂ + 1); linarith
  have hpb : 0 < p b := hT b (le_max_left _ _)
  obtain ⟨η₀, ⟨h01, h02⟩, hpz⟩ := intermediate_value_Icc hb2.le (cont_of hp h0)
    (show (0 : ℝ) ∈ Icc (p η₂) (p b) from ⟨by linarith, hpb.le⟩)
  have h0lt : η₂ < η₀ := lt_of_le_of_ne h01 (fun h => by rw [← h] at hpz; linarith)
  have hη₀0 : 0 ≤ η₀ := h0.trans h01
  have hpneg : ∀ y, η₂ ≤ y → y < η₀ → p y < 0 := fun y h1 h2 => by
    have := hsm η₀ ⟨h1, h2.le⟩ ⟨h01, le_rfl⟩ h2; rwa [hpz] at this
  have hppos : ∀ y, η₀ < y → 0 < p y := fun y h => by
    have := hsm y ⟨h01, h.le⟩ ⟨h01.trans h.le, le_rfl⟩ h; rwa [hpz] at this
  have hfa : StrictAntiOn f (Icc η₂ η₀) := santi hf h0 (fun x hx => hpneg x hx.1.le hx.2)
  have hfneg : ∀ y, η₂ < y → y ≤ η₀ → f y < 0 := fun y h1 h2 => by
    have := hfa ⟨le_rfl, h01⟩ ⟨h1.le, h2⟩ h1; linarith
  have hΦ := phider hf hp hq hW
  have hΦa := santi hΦ h0 (a := η₂) (b := η₀) (fun x hx => by
    have hqx := hafter x hx.1
    have hfx := hfneg x hx.1 hx.2.le
    have hpx := hpneg x hx.1.le hx.2
    have hfp : 0 < f x * p x := mul_pos_of_neg_of_neg hfx hpx
    have : 0 < q x + 2 * (K - 1) * f x * p x := by nlinarith
    have := mul_pos (mul_pos (hWpos x) hqx) this
    linarith)
  have hlt := hΦa ⟨le_rfl, h01⟩ ⟨h01, le_rfl⟩ h0lt
  simp only [hq2, hpz] at hlt
  have hW2 := hWpos η₂
  have hW0 := hWpos η₀
  have hf0 := hfneg η₀ h0lt le_rfl
  have hr0 : 0 < -(K * f η₀ * q η₀) - 1 + p η₀ ^ 2 := by
    by_contra hc
    push Not at hc
    have h1 : 0 ≤ f η₀ * (-(K * f η₀ * q η₀) - 1 + p η₀ ^ 2) := mul_nonneg_of_nonpos_of_nonpos hf0.le hc
    have h2 : f η₂ * (-(K * f η₂ * 0) - 1 + p η₂ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hf2 (by nlinarith)
    have h3 := mul_nonneg hW0.le h1
    have h4 := mul_nonpos_of_nonneg_of_nonpos hW2.le h2
    rw [hpz] at h3
    norm_num at hlt h3 h4
    linarith
  have hq0 : 0 < q η₀ := hafter η₀ h0lt
  set b' := η₀ + 2 / q η₀ with hb'
  have hb'0 : η₀ < b' := by have : 0 < 2 / q η₀ := by positivity
                            linarith
  -- W r is monotone on [η₀, b'], so r > 0 there
  have hWr := mono (wrder hf hp hq hW) hη₀0 (a := η₀) (b := b') (fun x hx => by
    have := mul_pos (mul_pos (hWpos x) (hppos x hx.1)) (hafter x (h0lt.trans hx.1))
    have h2K : 0 ≤ 2 - K := by linarith
    have := mul_nonneg h2K this.le
    linarith [show (2 - K) * W x * p x * q x = (2 - K) * (W x * p x * q x) by ring])
  have hrpos : ∀ x ∈ Icc η₀ b', 0 < -(K * f x * q x) - 1 + p x ^ 2 := by
    intro x hx
    have h1 := hWr ⟨le_rfl, hb'0.le⟩ hx hx.1
    have h2 := mul_pos hW0 hr0
    exact pos_of_mul_pos_right (h2.trans_le h1) (hWpos x).le
  have hqm := mono hq hη₀0 (a := η₀) (b := b') (fun x hx => (hrpos x ⟨hx.1.le, hx.2.le⟩).le)
  have hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun y => p y - q η₀ * y) (q η - q η₀ * 1) (Ici 0) η :=
    fun η hη => (hp η hη).sub ((hasDerivWithinAt_id η _).const_mul (q η₀))
  have hgm := mono hg hη₀0 (a := η₀) (b := b') (fun x hx => by
    have := hqm ⟨le_rfl, hb'0.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1.le
    linarith)
  have h := hgm ⟨le_rfl, hb'0.le⟩ ⟨hb'0.le, le_rfl⟩ hb'0.le
  simp only [hpz] at h
  have h2 : q η₀ * b' = q η₀ * η₀ + 2 := by
    rw [hb']; field_simp
  have := hle1 b' (hη₀0.trans hb'0.le)
  linarith

/-- L6 core: at a point ηd after which q < 0 up to η₂, with p ηd ≤ 0 and p ηd q ηd = 0, f η₂ ≥ 0
forces r ηd > 0 (1 ≤ K). -/
theorem descent_core {K : ℝ} (hK1 : 1 ≤ K) {f p q W : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hWpos : ∀ η, 0 < W η) (hW : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt W (K * f η * W η) (Ici 0) η)
    {ηd η₂ : ℝ} (hd0 : 0 ≤ ηd) (hd2 : ηd < η₂) (hneg : ∀ y, ηd < y → y < η₂ → q y < 0)
    (hq2 : q η₂ = 0) (hp2 : p η₂ ≤ -1) (hpd : p ηd ≤ 0) (hpq : p ηd * q ηd = 0)
    (hf2 : 0 ≤ f η₂) : 0 < -(K * f ηd * q ηd) - 1 + p ηd ^ 2 := by
  have hpa : StrictAntiOn p (Icc ηd η₂) := santi hp hd0 (fun x hx => hneg x hx.1 hx.2)
  have hpneg : ∀ y, ηd < y → y ≤ η₂ → p y < 0 := fun y h1 h2 => by
    have := hpa ⟨le_rfl, hd2.le⟩ ⟨h1.le, h2⟩ h1; linarith
  have hfa : StrictAntiOn f (Icc ηd η₂) := santi hf hd0 (fun x hx => hpneg x hx.1 hx.2.le)
  have hfpos : ∀ y, ηd ≤ y → y < η₂ → 0 < f y := fun y h1 h2 => by
    have := hfa ⟨h1, h2.le⟩ ⟨hd2.le, le_rfl⟩ h2; linarith
  have hΦa := santi (phider hf hp hq hW) hd0 (a := ηd) (b := η₂) (fun x hx => by
    have hqx := hneg x hx.1 hx.2
    have hfx := hfpos x hx.1.le hx.2
    have hpx := hpneg x hx.1 hx.2.le
    have hfp : f x * p x < 0 := mul_neg_of_pos_of_neg hfx hpx
    have : q x + 2 * (K - 1) * f x * p x < 0 := by nlinarith
    have := mul_pos (hWpos x) (mul_pos_of_neg_of_neg hqx this)
    linarith [show W x * q x * (q x + 2 * (K - 1) * f x * p x)
      = W x * (q x * (q x + 2 * (K - 1) * f x * p x)) by ring])
  have hlt := hΦa ⟨le_rfl, hd2.le⟩ ⟨hd2.le, le_rfl⟩ hd2
  simp only [hq2, hpq] at hlt
  have hfd := hfpos ηd le_rfl hd2
  have h2 : 0 ≤ f η₂ * (-(K * f η₂ * 0) - 1 + p η₂ ^ 2) := mul_nonneg hf2 (by nlinarith)
  have h4 := mul_nonneg (hWpos η₂).le h2
  have h5 : 0 < W ηd * (f ηd * (-(K * f ηd * q ηd) - 1 + p ηd ^ 2)) := by
    simp only [mul_zero, sub_zero] at hlt h4; linarith
  exact pos_of_mul_pos_right (pos_of_mul_pos_right h5 (hWpos ηd).le) hfd.le

/-- L6 (Descent, 1 ≤ K ≤ 2). -/
theorem descent {K : ℝ} (hK1 : 1 ≤ K) (hK2 : K ≤ 2) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    {ηz η₂ : ℝ} (hz0 : 0 ≤ ηz) (hz2 : ηz < η₂) (hneg : ∀ y, ηz < y → y < η₂ → q y < 0)
    (hq2 : q η₂ = 0) (hp2 : p η₂ ≤ -1) (hrz : -(K * f ηz * q ηz) - 1 + p ηz ^ 2 ≤ 0)
    (hpq : p ηz * q ηz = 0) : f η₂ < 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨W, hWpos, hW⟩ := weight hf K
  by_cases hpz : p ηz ≤ 0
  · exact absurd (descent_core hK1 hf hp hq hWpos hW hz0 hz2 hneg hq2 hp2 hpz hpq hc) (not_lt.2 hrz)
  push Not at hpz
  have hpa : StrictAntiOn p (Icc ηz η₂) := santi hp hz0 (fun x hx => hneg x hx.1 hx.2)
  obtain ⟨ηd, ⟨hd1, hd2⟩, hpd⟩ := intermediate_value_Icc' hz2.le (cont_of hp hz0)
    (show (0 : ℝ) ∈ Icc (p η₂) (p ηz) from ⟨by linarith, hpz.le⟩)
  have hzd : ηz < ηd := lt_of_le_of_ne hd1 (fun h => by rw [← h] at hpd; linarith)
  have hd2' : ηd < η₂ := lt_of_le_of_ne hd2 (fun h => by rw [h] at hpd; linarith)
  have hr := descent_core hK1 hf hp hq hWpos hW (hz0.trans hd1) hd2'
    (fun y h1 h2 => hneg y (hzd.trans h1) h2) hq2 hp2 hpd.le (by rw [hpd]; ring) hc
  have hWr := anti (wrder hf hp hq hW) hz0 (a := ηz) (b := ηd) (fun x hx => by
    have hpx : 0 < p x := by
      have := hpa ⟨hx.1.le, hx.2.le.trans hd2⟩ ⟨hd1, hd2⟩ hx.2; rwa [hpd] at this
    have hqx := hneg x hx.1 (hx.2.trans hd2')
    have := mul_neg_of_pos_of_neg (mul_pos (hWpos x) hpx) hqx
    have h2K : 0 ≤ 2 - K := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos h2K this.le
    linarith [show (2 - K) * W x * p x * q x = (2 - K) * (W x * p x * q x) by ring])
  have h1 := hWr ⟨le_rfl, hd1⟩ ⟨hd1, le_rfl⟩ hd1
  have h2 := mul_pos (hWpos ηd) hr
  have h3 := mul_nonpos_of_nonneg_of_nonpos (hWpos ηz).le hrz
  linarith

/-- L8 (K ≥ 2). -/
theorem omega {K : ℝ} (hK2 : 2 ≤ K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hlim : Tendsto p atTop (𝓝 1)) (hle1 : ∀ η ∈ Ici (0 : ℝ), p η ≤ 1)
    {η₂ : ℝ} (h0 : 0 ≤ η₂) (hq2 : q η₂ = 0) (hp2 : 1 ≤ p η₂ ^ 2)
    (hafter : ∀ y, η₂ < y → 0 < q y) : False := by
  obtain ⟨M, hMpos, hM⟩ := weight hf 2
  have hM' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt M (2 * f η * M η) (Ici 0) η := hM
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (hlim.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)))
  set T' := max T η₂ with hT'
  have hT'0 : 0 ≤ T' := h0.trans (le_max_right _ _)
  set B := T' + 2 * |f T'| + 2 with hB
  have hTB : T' < B := by have := abs_nonneg (f T'); linarith
  have hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun y => f y - 1 / 2 * y) (p η - 1 / 2 * 1) (Ici 0) η :=
    fun η hη => (hf η hη).sub ((hasDerivWithinAt_id η _).const_mul (1 / 2))
  have hgm := mono hg hT'0 (a := T') (b := B) (fun x hx => by
    have := hT x ((le_max_left _ _).trans hx.1.le); linarith)
  have h1 := hgm ⟨le_rfl, hTB.le⟩ ⟨hTB.le, le_rfl⟩ hTB.le
  have hfB : 0 < f B := by
    have := neg_abs_le (f T'); simp only at h1; linarith
  have hη₂B : η₂ < B := lt_of_le_of_lt (le_max_right _ _) hTB
  have hΩ := mono (omder hf hp hq hM') h0 (a := η₂) (b := B) (fun x hx =>
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (hMpos x).le) (sq_nonneg _))
      (hafter x hx.1).le)
  have h2 := hΩ ⟨le_rfl, hη₂B.le⟩ ⟨hη₂B.le, le_rfl⟩ hη₂B.le
  simp only [hq2, mul_zero, sub_zero] at h2
  have hpB : 1 / 2 < p B := hT B ((le_max_left _ _).trans hTB.le)
  have hpB1 := hle1 B (hT'0.trans hTB.le)
  have hqB := hafter B hη₂B
  have h3 : p B ^ 2 - 1 - 2 * f B * q B < 0 := by nlinarith [mul_pos hfB hqB]
  have h4 := mul_neg_of_pos_of_neg (hMpos B) h3
  have h5 := mul_nonneg (hMpos η₂).le (show 0 ≤ p η₂ ^ 2 - 1 by linarith)
  linarith

/-- Main theorem (K ≥ 1): every solution with f(0) = 0, p(0) = 0, p → 1 that never touches the
lines p = ±1 with q = 0 has q > 0 on [0, ∞). The touching condition is discharged by ODE
uniqueness in `touch`. -/
theorem q_pos_of_touch {K : ℝ} (hK : 1 ≤ K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (htouch : ∀ η ∈ Ici (0 : ℝ), q η = 0 → p η ≠ 1 ∧ p η ≠ -1) :
    ∀ η ∈ Ici (0 : ℝ), 0 < q η := by
  have hle1 := le_one hp hq (by rw [hp0]; norm_num) hlim
  have hlt1 : ∀ η ∈ Ici (0 : ℝ), p η < 1 := by
    intro η hη
    refine lt_of_le_of_ne (hle1 η hη) (fun he => ?_)
    have hpos : 0 < η := by
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ η from hη) with h | h
      · rw [← h, hp0] at he; norm_num at he
      · exact h
    have hq0 := q_zero_of_max hp hpos (fun y hy => he ▸ hle1 y hy)
    exact (htouch η hη hq0).1 he
  intro η₁ hη₁
  by_contra hcon
  have hq₁ : q η₁ ≤ 0 := not_lt.1 hcon
  obtain ⟨η₂, c, hη₂, hc0, hc2, hq2, hp2, hafter, hbefore⟩ :=
    last_zero hp hq hp0 hlim hlt1 (fun η hη hqη => (htouch η hη hqη).2) hη₁ hq₁
  rcases le_total 2 K with hK2 | hK2
  · exact omega hK2 hf hp hq hlim hle1 hη₂.le hq2 (by nlinarith) hafter
  set S := Icc 0 c ∩ q ⁻¹' Ici 0 with hS
  have hScl : IsClosed S := (cont_of hq le_rfl).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  have hqc : q c < 0 := hbefore c le_rfl hc2
  by_cases hne : S.Nonempty
  · set ηz := sSup S with hηz
    have hmem : ηz ∈ S := hSc.sSup_mem hne
    have hz0 : 0 ≤ ηz := hmem.1.1
    have hzc : ηz < c := lt_of_le_of_ne hmem.1.2 (fun h => by
      have := hmem.2; rw [h] at this; exact absurd (show (0 : ℝ) ≤ q c from this) (not_le.2 hqc))
    have hneg : ∀ y, ηz < y → y < η₂ → q y < 0 := by
      intro y h1 h2
      rcases le_or_gt c y with hy | hy
      · exact hbefore y hy h2
      · by_contra hc'
        push Not at hc'
        have : y ∈ S := ⟨⟨hz0.trans h1.le, hy.le⟩, hc'⟩
        exact absurd (le_csSup hSc.bddAbove this) (not_le.2 h1)
    have hqd : HasDerivWithinAt q (-(K * f ηz * q ηz) - 1 + p ηz ^ 2) (Ici ηz) ηz :=
      (hq ηz hz0).mono (Ici_subset_Ici.2 hz0)
    have hev : ∀ᶠ y in 𝓝[>] ηz, q y < 0 := by
      filter_upwards [Ioo_mem_nhdsGT (hzc.trans hc2)] with y hy
      exact hneg y hy.1 hy.2
    have hqz : q ηz = 0 := le_antisymm
      (le_of_right hqd.continuousWithinAt (by filter_upwards [hev] with y hy; exact hy.le))
      hmem.2
    have hrz := right_nonpos hqd (by filter_upwards [hev] with y hy; rw [hqz]; exact hy.le)
    have hfz := descent hK hK2 hf hp hq hz0 (hzc.trans hc2) hneg hq2 hp2.le hrz (by rw [hqz]; ring)
    exact ascent hK hK2 hf hp hq hlim hle1 hη₂.le hq2 hp2.le hfz.le hafter
  · have hneg : ∀ y, 0 < y → y < η₂ → q y < 0 := by
      intro y h1 h2
      rcases le_or_gt c y with hy | hy
      · exact hbefore y hy h2
      · by_contra hc'
        push Not at hc'
        exact hne ⟨y, ⟨h1.le, hy.le⟩, hc'⟩
    have hfz := descent hK hK2 hf hp hq le_rfl hη₂ hneg hq2 hp2.le
      (by rw [hf0, hp0]; norm_num) (by rw [hp0]; ring)
    exact ascent hK hK2 hf hp hq hlim hle1 hη₂.le hq2 hp2.le hfz.le hafter



open Checked.FalknerSkan.BoundedTools in
/-- L3 (touch): a solution with p(0) = 0 never has q = 0 together with p = ±1 (backward
uniqueness against the straight line (f η₁ + s (t − η₁), s, 0)). -/
theorem touch_one {K s : ℝ} (hs : s = 1 ∨ s = -1) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    {η₁ : ℝ} (hη₁ : 0 < η₁) (hq1 : q η₁ = 0) (htouch : p η₁ = s) : p 0 = s := by
  have hnhds : ∀ t, 0 < t → Ici (0 : ℝ) ∈ 𝓝 t := fun t ht => Ici_mem_nhds ht
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  set Z : ℝ → ℝ × ℝ × ℝ := fun t => (f η₁ + s * (t - η₁), s, 0) with hZ
  have hZd : ∀ t, HasDerivAt Z (fsV K (Z t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f η₁ + s * (t - η₁)) s t := by
      simpa using ((hasDerivAt_id t).sub_const η₁).const_mul s |>.const_add (f η₁)
    have := h1.prodMk ((hasDerivAt_const t s).prodMk (hasDerivAt_const t (0 : ℝ)))
    convert this using 1
    simp only [fsV, hZ, mul_zero, neg_zero, zero_sub, hs2]
    norm_num
  have key := uniq_left (fsV_lip K) (a := 0) (b := η₁) (triple_cont hf hp hq η₁)
    (fun t ht => ((triple hf hp hq t ht.1.le).hasDerivAt (hnhds t ht.1)).hasDerivWithinAt)
    (fun t _ => (hZd t).continuousAt.continuousWithinAt)
    (fun t _ => (hZd t).hasDerivWithinAt)
    (by simp only [hZ, sub_self, mul_zero, add_zero, htouch, hq1]) ⟨le_rfl, hη₁.le⟩
  simp only [hZ, Prod.mk.injEq] at key
  exact key.2.1

theorem touch {K : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hp0 : p 0 = 0) : ∀ η ∈ Ici (0 : ℝ), q η = 0 → p η ≠ 1 ∧ p η ≠ -1 := by
  intro η hη hq0
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ η from hη) with h | hpos
  · subst h; rw [hp0]; norm_num
  refine ⟨fun he => ?_, fun he => ?_⟩
  · have := touch_one (Or.inl rfl) hf hp hq hpos hq0 he
    rw [hp0] at this; norm_num at this
  · have := touch_one (Or.inr rfl) hf hp hq hpos hq0 he
    rw [hp0] at this; norm_num at this

/-- Every solution of f' = p, p' = q, q' = −K f q − 1 + p² (K ≥ 1) on [0, ∞) with f(0) = 0,
p(0) = 0 and p → 1 has q > 0 on [0, ∞). -/
theorem q_pos {K : ℝ} (hK : 1 ≤ K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), 0 < q η :=
  q_pos_of_touch hK hf hp hq hf0 hp0 hlim (touch hf hp hq hp0)

/-- The class −1 ≤ p ≤ 1 follows. -/
theorem in_class {K : ℝ} (hK : 1 ≤ K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := by
  intro η hη
  have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim (q_pos hK hf hp hq hf0 hp0 hlim) η hη
  exact ⟨by linarith [h.1], h.2.le⟩

end Work.FalknerSkan.UnrestrictedCore
