import Mathlib

/-!
# Townes existence: the critical solution is a ground state

Pure analysis for the shooting argument (run 2026-11-07T0628Z). A solution of the Townes radial
equation θ'' + (1/r)θ' − θ + θ³ = 0 with θ(0) > 1, φ = θ' negative near 0, no degenerate zero
((θ, φ) ≠ (0, 0), (1, 0) at r > 0) and neither shooting event (φ turning positive while θ > 0;
θ turning negative while φ < 0) stays positive and strictly decreasing and tends to 0.

Positivity: at the first time T where φ < 0 ∧ θ > 0 fails, the sign of θ' or φ' at T produces
one of the two events or a contradiction. Limit: θ decreases to L ≥ 0; L ≥ 1 is excluded since
(rφ)' = r(θ − θ³) < 0 gives φ ≤ −k/r and θ ≤ θ(1) − k log r; 0 < L < 1 is excluded since then
φ' ≥ θ − θ³ ≥ c > 0 eventually.
-/

namespace Work.Townes.TExLimit
open Set Filter Topology

theorem right_lt {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) (hd : d < 0) :
    ∀ᶠ t in 𝓝[>] x, f t < f x := by
  have h := hasDerivAt_iff_tendsto_slope.1 hf
  have h' : Tendsto (slope f x) (𝓝[>] x) (𝓝 d) :=
    h.mono_left (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  filter_upwards [h'.eventually (gt_mem_nhds hd), self_mem_nhdsWithin] with t ht htx
  rw [slope_def_field] at ht
  have htx' : 0 < t - x := sub_pos.2 htx
  by_contra hc
  push Not at hc
  have := div_nonneg (sub_nonneg.2 hc) htx'.le
  linarith

theorem right_gt {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] x, f x < f t := by
  have h := hasDerivAt_iff_tendsto_slope.1 hf
  have h' : Tendsto (slope f x) (𝓝[>] x) (𝓝 d) :=
    h.mono_left (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  filter_upwards [h'.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with t ht htx
  rw [slope_def_field] at ht
  have htx' : 0 < t - x := sub_pos.2 htx
  by_contra hc
  push Not at hc
  have := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hc) htx'.le
  linarith

theorem left_gt {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) (hd : d < 0) :
    ∀ᶠ t in 𝓝[<] x, f x < f t := by
  have h := hasDerivAt_iff_tendsto_slope.1 hf
  have h' : Tendsto (slope f x) (𝓝[<] x) (𝓝 d) :=
    h.mono_left (nhdsWithin_mono _ (fun t ht => ne_of_lt ht))
  filter_upwards [h'.eventually (gt_mem_nhds hd), self_mem_nhdsWithin] with t ht htx
  rw [slope_def_field] at ht
  have htx' : t - x < 0 := sub_neg.2 htx
  by_contra hc
  push Not at hc
  have := div_nonneg_of_nonpos (sub_nonpos.2 hc) htx'.le
  linarith

/-- A ball around `x` on which `p` holds, from an eventual statement. -/
theorem ball_of_eventually {p : ℝ → Prop} {x : ℝ} (h : ∀ᶠ y in 𝓝 x, p y) :
    ∃ ε > 0, ∀ y, |y - x| < ε → p y := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 h
  exact ⟨ε, hε, fun y hy => h (by rwa [Real.dist_eq])⟩

section
variable (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r)
    (hφ : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r)

include hθ in
theorem θ_hasDerivAt {r : ℝ} (hr : 0 < r) : HasDerivAt θ (φ r) r :=
  (hθ r (le_of_lt hr)).hasDerivAt (Ici_mem_nhds hr)

include hθ hφ in
theorem pos_neg (hθ0 : 1 < θ 0)
    (hnear : ∃ δ > 0, ∀ r ∈ Ioc (0 : ℝ) δ, φ r < 0)
    (hz : ∀ r ∈ Ioi (0 : ℝ), θ r = 0 → φ r = 0 → False)
    (h1 : ∀ r ∈ Ioi (0 : ℝ), θ r = 1 → φ r = 0 → False)
    (notU : ¬ ∃ t ∈ Ioi (0 : ℝ), 0 < φ t ∧ ∀ s ∈ Icc 0 t, 0 < θ s)
    (notO : ¬ ∃ t ∈ Ioi (0 : ℝ), θ t < 0 ∧ ∀ s ∈ Ioc 0 t, φ s < 0) :
    ∀ t ∈ Ioi (0 : ℝ), φ t < 0 ∧ 0 < θ t := by
  -- a good initial interval
  obtain ⟨δ, hδ, hδφ⟩ := hnear
  have hc0 : ContinuousWithinAt θ (Ici 0) 0 := (hθ 0 (mem_Ici.2 le_rfl)).continuousWithinAt
  have hev := hc0.eventually (lt_mem_nhds hθ0)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hε₀'⟩ := ball_of_eventually hev
  set δ0 := min δ (ε₀ / 2) with hδ0def
  have hδ0 : 0 < δ0 := lt_min hδ (by linarith)
  have hgood : ∀ s ∈ Ioc (0 : ℝ) δ0, φ s < 0 ∧ 0 < θ s := by
    intro s hs
    refine ⟨hδφ s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩, ?_⟩
    have h2 : s ≤ ε₀ / 2 := hs.2.trans (min_le_right _ _)
    have := hε₀' s (by rw [abs_lt]; constructor <;> linarith [hs.1]) (le_of_lt hs.1)
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨b₀, hb₀, hb₀'⟩ := hcon
  let B : Set ℝ := {t | 0 < t ∧ ¬ (φ t < 0 ∧ 0 < θ t)}
  have hBne : B.Nonempty := ⟨b₀, hb₀, fun h => by linarith [hb₀' h.1]⟩
  have hBbdd : BddBelow B := ⟨0, fun b hb => le_of_lt hb.1⟩
  have hBgt : ∀ b ∈ B, δ0 < b := by
    intro b hb
    by_contra h; push Not at h
    exact hb.2 (hgood b ⟨hb.1, h⟩)
  set T := sInf B with hTdef
  have hTδ : δ0 ≤ T := le_csInf hBne (fun b hb => (hBgt b hb).le)
  have hT0 : 0 < T := lt_of_lt_of_le hδ0 hTδ
  have hbelow : ∀ s ∈ Ioo (0 : ℝ) T, φ s < 0 ∧ 0 < θ s := by
    intro s hs
    by_contra h
    have := csInf_le hBbdd (show s ∈ B from ⟨hs.1, h⟩)
    linarith [hs.2]
  have hθc : ContinuousAt θ T := (θ_hasDerivAt θ φ hθ hT0).continuousAt
  have hφc : ContinuousAt φ T := (hφ T hT0).continuousAt
  have hIoo : Ioo 0 T ∈ 𝓝[<] T := Ioo_mem_nhdsLT hT0
  have hφT : φ T ≤ 0 := by
    refine le_of_tendsto (hφc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio T))) ?_
    filter_upwards [hIoo] with s hs using (hbelow s hs).1.le
  have hθT : 0 ≤ θ T := by
    refine ge_of_tendsto (hθc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio T))) ?_
    filter_upwards [hIoo] with s hs using (hbelow s hs).2.le
  have hnot : ¬ (φ T < 0 ∧ 0 < θ T) := by
    rintro ⟨ha, hb⟩
    obtain ⟨ε, hε, hball⟩ := ball_of_eventually
      ((hφc.eventually (gt_mem_nhds ha)).and (hθc.eventually (lt_mem_nhds hb)))
    have : T + ε ≤ T := by
      rw [hTdef]
      refine le_csInf hBne (fun b hb => ?_)
      have hTb : T ≤ b := csInf_le hBbdd hb
      by_contra hlt; push Not at hlt
      exact hb.2 (hball b (by rw [abs_lt]; constructor <;> linarith))
    linarith
  -- φ and θ near T
  rcases hθT.lt_or_eq with hθTp | hθT0
  · -- θ T > 0, so φ T = 0
    have hφT0 : φ T = 0 := by
      by_contra h
      exact hnot ⟨lt_of_le_of_ne hφT h, hθTp⟩
    have hd : -(1 / T * φ T) + θ T - θ T ^ 3 = θ T * (1 - θ T ^ 2) := by rw [hφT0]; ring
    have hφd := hφ T hT0
    rw [hd] at hφd
    obtain ⟨ε, hε, hball⟩ := ball_of_eventually (hθc.eventually (lt_mem_nhds hθTp))
    rcases lt_trichotomy (θ T) 1 with hlt | heq | hgt
    · have hdpos : 0 < θ T * (1 - θ T ^ 2) := by
        apply mul_pos hθTp; nlinarith
      have hev := right_gt hφd hdpos
      obtain ⟨t, ht1, ht2⟩ := (hev.and (Ioo_mem_nhdsGT (show T < T + ε by linarith))).exists
      rw [hφT0] at ht1
      refine notU ⟨t, lt_trans hT0 ht2.1, ht1, fun s hs => ?_⟩
      rcases hs.1.lt_or_eq with hs0 | hs0
      · rcases lt_or_ge s T with hsT | hsT
        · exact (hbelow s ⟨hs0, hsT⟩).2
        · exact hball s (by rw [abs_lt]; constructor <;> linarith [ht2.2, hs.2])
      · rw [← hs0]; linarith
    · exact h1 T hT0 heq hφT0
    · have hdneg : θ T * (1 - θ T ^ 2) < 0 := by
        apply mul_neg_of_pos_of_neg hθTp; nlinarith
      have hev := left_gt hφd hdneg
      obtain ⟨t, ht1, ht2⟩ := (hev.and hIoo).exists
      rw [hφT0] at ht1
      linarith [(hbelow t ht2).1]
  · -- θ T = 0
    have hφTneg : φ T < 0 := by
      rcases hφT.lt_or_eq with h | h
      · exact h
      · exact (hz T hT0 hθT0.symm h).elim
    obtain ⟨ε, hε, hball⟩ := ball_of_eventually (hφc.eventually (gt_mem_nhds hφTneg))
    have hev := right_lt (θ_hasDerivAt θ φ hθ hT0) hφTneg
    obtain ⟨t, ht1, ht2⟩ := (hev.and (Ioo_mem_nhdsGT (show T < T + ε by linarith))).exists
    rw [← hθT0] at ht1
    refine notO ⟨t, lt_trans hT0 ht2.1, ht1, fun s hs => ?_⟩
    rcases lt_or_ge s T with hsT | hsT
    · exact (hbelow s ⟨hs.1, hsT⟩).1
    · exact hball s (by rw [abs_lt]; constructor <;> linarith [ht2.2, hs.2])

end

theorem limit (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r)
    (hφ : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r)
    (hθ0 : 1 < θ 0)
    (hnear : ∃ δ > 0, ∀ r ∈ Ioc (0 : ℝ) δ, φ r < 0)
    (hz : ∀ r ∈ Ioi (0 : ℝ), θ r = 0 → φ r = 0 → False)
    (h1 : ∀ r ∈ Ioi (0 : ℝ), θ r = 1 → φ r = 0 → False)
    (notU : ¬ ∃ t ∈ Ioi (0 : ℝ), 0 < φ t ∧ ∀ s ∈ Icc 0 t, 0 < θ s)
    (notO : ¬ ∃ t ∈ Ioi (0 : ℝ), θ t < 0 ∧ ∀ s ∈ Ioc 0 t, φ s < 0) :
    (∀ r ∈ Ici (0 : ℝ), 0 < θ r) ∧ (∀ r ∈ Ioi (0 : ℝ), φ r < 0) ∧ Tendsto θ atTop (𝓝 0) := by
  have hPN := pos_neg θ φ hθ hφ hθ0 hnear hz h1 notU notO
  have hpos : ∀ r ∈ Ici (0 : ℝ), 0 < θ r := by
    intro r hr
    rcases (mem_Ici.1 hr).lt_or_eq with h | h
    · exact (hPN r h).2
    · rw [← h]; linarith
  have hneg : ∀ r ∈ Ioi (0 : ℝ), φ r < 0 := fun r hr => (hPN r hr).1
  refine ⟨hpos, hneg, ?_⟩
  -- θ is strictly decreasing on [0, ∞)
  have hanti : StrictAntiOn θ (Ici 0) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (f' := φ) (convex_Ici 0)
      (fun x hx => (hθ x hx).continuousWithinAt)
      (fun x hx => (hθ x (interior_subset hx)).mono interior_subset) (fun x hx => ?_)
    rw [interior_Ici] at hx; exact hneg x hx
  have hne : (θ '' Ici (0 : ℝ)).Nonempty := ⟨θ 0, 0, mem_Ici.2 le_rfl, rfl⟩
  have hbdd : BddBelow (θ '' Ici (0 : ℝ)) := ⟨0, by rintro _ ⟨r, hr, rfl⟩; exact (hpos r hr).le⟩
  set L := sInf (θ '' Ici (0 : ℝ)) with hLdef
  have hL : ∀ r ∈ Ici (0 : ℝ), L ≤ θ r := fun r hr => csInf_le hbdd ⟨r, hr, rfl⟩
  have hL0 : 0 ≤ L := le_csInf hne (by rintro _ ⟨r, hr, rfl⟩; exact (hpos r hr).le)
  have htend : Tendsto θ atTop (𝓝 L) := by
    rw [tendsto_order]; constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop 0] with r hr
      exact lt_of_lt_of_le ha (hL r hr)
    · intro a ha
      obtain ⟨_, ⟨r₀, hr₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne ha
      filter_upwards [eventually_ge_atTop r₀] with r hr
      exact lt_of_le_of_lt (hanti.antitoneOn hr₀ (mem_Ici.2 ((mem_Ici.1 hr₀).trans hr)) hr) hlt
  suffices hL00 : L = 0 by rw [← hL00]; exact htend
  by_contra hLne
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hLne)
  have hθd : ∀ r, 0 < r → HasDerivAt θ (φ r) r := fun r hr => θ_hasDerivAt θ φ hθ hr
  rcases le_or_gt 1 L with hL1 | hL1
  · -- L ≥ 1
    have hgt1 : ∀ r ∈ Ici (0 : ℝ), 1 < θ r := by
      intro r hr
      have hr1 : r + 1 ∈ Ici (0 : ℝ) := mem_Ici.2 (by linarith [mem_Ici.1 hr])
      have := hanti hr hr1 (by linarith)
      linarith [hL _ hr1]
    have hPd : ∀ r, 0 < r → HasDerivAt (fun r => r * φ r) (r * (θ r - θ r ^ 3)) r := by
      intro r hr
      have := (hasDerivAt_id' r).mul (hφ r hr)
      convert this using 1
      field_simp
      ring
    have hPanti : AntitoneOn (fun r => r * φ r) (Ici 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun r => r * (θ r - θ r ^ 3))
        (convex_Ici 1)
        (fun x hx => (hPd x (by linarith [mem_Ici.1 hx])).continuousAt.continuousWithinAt)
        (fun x hx => ?_) (fun x hx => ?_)
      · rw [interior_Ici] at hx
        exact (hPd x (by linarith [mem_Ioi.1 hx])).hasDerivWithinAt
      · rw [interior_Ici] at hx
        have hx0 : 0 < x := by linarith [mem_Ioi.1 hx]
        have h1x := hgt1 x (mem_Ici.2 hx0.le)
        have : θ x - θ x ^ 3 ≤ 0 := by
          have hsq : 1 ≤ θ x ^ 2 := by nlinarith
          have : θ x - θ x ^ 3 = θ x * (1 - θ x ^ 2) := by ring
          rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        exact mul_nonpos_of_nonneg_of_nonpos hx0.le this
    set k := -φ 1 with hk
    have hk0 : 0 < k := by have := hneg 1 (by norm_num); linarith
    have hφle : ∀ r, 1 ≤ r → φ r ≤ -(k * r⁻¹) := by
      intro r hr
      have hr0 : 0 < r := by linarith
      have := hPanti (mem_Ici.2 le_rfl) (mem_Ici.2 hr) hr
      simp only [one_mul] at this
      have e : -(k * r⁻¹) = -k / r := by field_simp
      rw [e, le_div_iff₀ hr0]
      linarith
    have hQd : ∀ r, 0 < r → HasDerivAt (fun r => θ r + k * Real.log r) (φ r + k * r⁻¹) r :=
      fun r hr => (hθd r hr).add ((Real.hasDerivAt_log hr.ne').const_mul k)
    have hQanti : AntitoneOn (fun r => θ r + k * Real.log r) (Ici 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun r => φ r + k * r⁻¹)
        (convex_Ici 1)
        (fun x hx => (hQd x (by linarith [mem_Ici.1 hx])).continuousAt.continuousWithinAt)
        (fun x hx => ?_) (fun x hx => ?_)
      · rw [interior_Ici] at hx
        exact (hQd x (by linarith [mem_Ioi.1 hx])).hasDerivWithinAt
      · rw [interior_Ici] at hx
        have := hφle x (le_of_lt (mem_Ioi.1 hx))
        linarith
    set R := Real.exp (θ 1 / k + 1) with hR
    have hθ1 : 0 < θ 1 := hpos 1 (mem_Ici.2 (by norm_num))
    have hR1 : 1 ≤ R := Real.one_le_exp (by positivity)
    have := hQanti (mem_Ici.2 le_rfl) (mem_Ici.2 hR1) hR1
    simp only [Real.log_one, mul_zero, add_zero, hR, Real.log_exp] at this
    have e : k * (θ 1 / k + 1) = θ 1 + k := by field_simp
    rw [e] at this
    have := hpos R (mem_Ici.2 (by linarith))
    linarith
  · -- 0 < L < 1
    set L' := (L + 1) / 2 with hL'
    have hLL' : L < L' := by linarith
    have hL'1 : L' < 1 := by linarith
    obtain ⟨a, ha⟩ := eventually_atTop.1 (htend.eventually (gt_mem_nhds hLL'))
    set r₀ := max a 1 with hr₀
    have hr₀1 : 1 ≤ r₀ := le_max_right _ _
    set c := L * (1 - L' ^ 2) with hc
    have hc0 : 0 < c := mul_pos hLpos (by nlinarith)
    have hφd' : ∀ r, r₀ ≤ r → c ≤ -(1 / r * φ r) + θ r - θ r ^ 3 := by
      intro r hr
      have hr0 : 0 < r := by linarith
      have hφr := hneg r hr0
      have h1' : 0 ≤ -(1 / r * φ r) := by
        have : 1 / r * φ r < 0 := mul_neg_of_pos_of_neg (by positivity) hφr
        linarith
      have hθr : θ r < L' := ha r (le_trans (le_max_left _ _) hr)
      have hθL : L ≤ θ r := hL r (mem_Ici.2 hr0.le)
      have h2 : 1 - L' ^ 2 ≤ 1 - θ r ^ 2 := by nlinarith
      have h3 : c ≤ θ r * (1 - θ r ^ 2) :=
        mul_le_mul hθL h2 (by nlinarith) (by linarith)
      nlinarith
    have hfmono : MonotoneOn (fun r => φ r - c * r) (Ici r₀) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun r => (-(1 / r * φ r) + θ r - θ r ^ 3) - c * 1) (convex_Ici r₀)
        (fun x hx => ((hφ x (by simp; linarith [mem_Ici.1 hx])).sub
          ((hasDerivAt_id x).const_mul c)).continuousAt.continuousWithinAt)
        (fun x hx => ?_) (fun x hx => ?_)
      · rw [interior_Ici] at hx
        exact ((hφ x (by simp; linarith [mem_Ioi.1 hx])).sub
          ((hasDerivAt_id x).const_mul c)).hasDerivWithinAt
      · rw [interior_Ici] at hx
        have := hφd' x (le_of_lt (mem_Ioi.1 hx))
        linarith
    set r1 := r₀ + (-φ r₀) / c + 1 with hr1
    have hφr₀ := hneg r₀ (by simp; linarith)
    have hr1ge : r₀ ≤ r1 := by
      have : 0 ≤ (-φ r₀) / c := div_nonneg (by linarith) hc0.le
      linarith
    have := hfmono (mem_Ici.2 le_rfl) (mem_Ici.2 hr1ge) hr1ge
    simp only at this
    have e : c * r1 = c * r₀ + (-φ r₀) + c := by
      rw [hr1]; field_simp
    have hφr1 := hneg r1 (by simp; linarith)
    linarith

end Work.Townes.TExLimit
