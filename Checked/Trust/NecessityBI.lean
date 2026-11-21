import Checked.Trust.NecessityAQ

/-!
# Hypothesis necessity, the four flat Lusso et al. 2019 headlines: the lower density bound (trust track T2b)

Run 2026-11-21T0028Z. The headlines `B1L19.l19_sq_central`, `l19_sqg_central`, `l19_sq_box` and `l19_sqg_box`
assume flat ΛCDM with matter density `0 ≤ Ω ≤ 1`. Their first hypothesis `0 ≤ Ω` is REDUNDANT: each
conclusion rests only on the lower bound of the distance ratio of the two sources that `delta_ge` proves for
`Ω ≥ 0`, and the same bound holds for every negative density the law admits.

* **Too negative a density cannot reach the farther source** (`bi_unreach`): where `Ω(1+z)³ + 1 − Ω < 0`
  the law gives a Hubble rate zero, so the scale factor cannot leave that region before the observation time
  (first time the radicand reaches half its value at the source, then the mean value theorem).
* **The bridge from the source on** (`bi_bridge`): the change of variables `v = √(a/a₀)` of `NCAQ.bridge`
  needs only a positive radicand at the source and `Ω ≤ 1` (the radicand then increases in `v`).
* **Comparison with the empty model** (`bi_lower`, `bi_upper`): for `Ω ≤ 0` the ratio of the integrand to
  the empty-model integrand two over `v³` decreases in `v`, so the integral below the nearer source's `v` gains
  at least as much as the one above it, each against the closed form of the empty model (`bi_int_cube`).
* **The ratio** (`bi_ratio`): a time where the scale factor is a quarter of its present value lies between the
  two sources (intermediate value); from it the distance to the farther source is more than three times the
  distance to the nearer one, above the bound used for `Ω ≥ 0`.
-/

namespace Checked.Trust.NCBI

open Set Filter Topology MeasureTheory Real
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1L19
open Checked.Trust.NCAQ

/-- Under the flat law the scale factor is monotone on the interval. -/
theorem bi_mono (Ω : ℝ) (a : ℝ → ℝ) (t t₀ : ℝ)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    MonotoneOn a (Icc t t₀) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc t t₀)
  · exact fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hdiff x (Ioo_subset_Icc_self hx)).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' := Ioo_subset_Icc_self hx
    have h1 := hH x hx'
    have h2 : 0 ≤ hubble a x := by rw [h1]; exact mul_nonneg hH₀.le (Real.sqrt_nonneg _)
    unfold hubble at h2
    exact (div_nonneg_iff.1 h2).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 (hpos x hx')))

/-- Where the radicand of the law is negative at the source, no scale factor obeys the law back to it. -/
theorem bi_unreach (Ω : ℝ) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hneg : Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω < 0) : False := by
  set f : ℝ → ℝ := fun s => Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω with hfdef
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨htt, le_rfl⟩
  have hf0 : f t₀ = 1 := by
    simp only [hfdef, redshift, div_self ha₀.ne']; ring
  have hfc : ContinuousOn f (Icc t t₀) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hc : ContinuousAt a x := (hdiff x hx).continuousAt
    have : ContinuousAt (fun s => a t₀ / a s) x := continuousAt_const.div hc (hpos x hx).ne'
    simp only [hfdef, redshift]
    fun_prop
  set c := f t / 2 with hc
  have hct : f t < c := by rw [hc]; linarith
  set K := {s ∈ Icc t t₀ | c ≤ f s} with hK
  have hKc : IsClosed K := hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hKne : K.Nonempty := ⟨t₀, ⟨htt, le_rfl⟩, by rw [hf0]; change f t / 2 ≤ 1; linarith⟩
  have hKb : BddBelow K := ⟨t, fun s hs => hs.1.1⟩
  set τ := sInf K with hτ
  have hτK : τ ∈ K := hKc.csInf_mem hKne hKb
  have htτ : t < τ := by
    rcases eq_or_lt_of_le hτK.1.1 with h | h
    · exfalso; have := hτK.2; rw [← h] at this; linarith
    · exact h
  have hzero : ∀ s ∈ Ico t τ, deriv a s = 0 := by
    intro s hs
    have hsI : s ∈ Icc t t₀ := ⟨hs.1, le_trans hs.2.le hτK.1.2⟩
    have hsK : s ∉ K := fun h => absurd (csInf_le hKb h) (not_le.2 hs.2)
    have hfs : f s < c := by
      by_contra h; exact hsK ⟨hsI, not_lt.1 h⟩
    have hneg' : Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω ≤ 0 := by
      change f s ≤ 0; linarith
    have := hH s hsI
    rw [Real.sqrt_eq_zero'.2 hneg', mul_zero] at this
    unfold hubble at this
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h (hpos s hsI).ne'
  obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope a htτ
    (fun x hx => (hdiff x ⟨hx.1, le_trans hx.2 hτK.1.2⟩).continuousAt.continuousWithinAt)
    (fun x hx => (hdiff x ⟨hx.1.le, le_trans hx.2.le hτK.1.2⟩).differentiableWithinAt)
  rw [hzero ξ ⟨hξ.1.le, hξ.2⟩] at hξd
  have hat : a τ = a t := by
    have hne : τ - t ≠ 0 := by linarith
    field_simp at hξd; linarith
  have hfτ : f τ = f t := by simp only [hfdef, redshift, hat]
  have := hτK.2
  rw [hfτ] at this
  linarith

/-- The bridge from the source on: a positive radicand at the source and `Ω ≤ 1` suffice. -/
theorem bi_bridge (Ω : ℝ) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hsrc : 0 < Ω + (1 - Ω) * √(a t / a t₀) ^ 6) :
    lumDistFlat a t₀ t = (1 + redshift a t₀ t) / hubble a t₀ *
      ∫ v in √(a t / a t₀)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  have hmono := bi_mono Ω a t t₀ hpos hdiff hH₀ hH
  set a₀ := a t₀ with ha₀def
  set H₀ := hubble a t₀ with hH₀def
  have ha₀ : 0 < a₀ := hpos t₀ ⟨htt, le_rfl⟩
  set v₀ := √(a t / a₀) with hv₀def
  have hv₀ : 0 < v₀ := Real.sqrt_pos.2 (div_pos (hpos t ⟨le_rfl, htt⟩) ha₀)
  have hinn : ∀ y, v₀ ≤ y → 0 < Ω + (1 - Ω) * y ^ 6 := by
    intro y hy
    have : v₀ ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ hv₀.le hy 6
    nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.2 hΩ₁)]
  set g : ℝ → ℝ := fun v => 2 / √(Ω + (1 - Ω) * v ^ 6) with hgdef
  set U : Set ℝ := {v | 0 < v ∧ 0 < Ω + (1 - Ω) * v ^ 6} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt continuous_const
        (by fun_prop : Continuous fun v : ℝ => Ω + (1 - Ω) * v ^ 6))
  have hgc : ContinuousOn g U := by
    intro v hv
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_const.div
    · exact (by fun_prop : Continuous fun v : ℝ => Ω + (1 - Ω) * v ^ 6).continuousAt.sqrt
    · exact (Real.sqrt_pos.2 hv.2).ne'
  set G : ℝ → ℝ := fun x => ∫ v in (1:ℝ)..x, g v with hGdef
  have hG : ∀ x, v₀ ≤ x → x ≤ 1 → HasDerivAt G (g x) x := by
    intro x hx hx1
    have hsub : uIcc (1:ℝ) x ⊆ U := by
      intro y hy
      rw [uIcc_of_ge hx1] at hy
      exact ⟨lt_of_lt_of_le hv₀ (le_trans hx hy.1), hinn y (le_trans hx hy.1)⟩
    have hxU : x ∈ U := hsub (by rw [uIcc_of_ge hx1]; exact ⟨le_rfl, hx1⟩)
    exact intervalIntegral.integral_hasDerivAt_right ((hgc.mono hsub).intervalIntegrable)
      (hgc.stronglyMeasurableAtFilter hUo x hxU) (hgc.continuousAt (hUo.mem_nhds hxU))
  set W : ℝ → ℝ := fun s => √(a s / a₀) with hWdef
  set F : ℝ → ℝ := fun s => G (W s) / (H₀ * a₀) with hFdef
  have hF : ∀ s ∈ uIcc t t₀, HasDerivAt F (1 / a s) s := by
    intro s hs
    rw [uIcc_of_le htt] at hs
    have has := hpos s hs
    have hr : 0 < a s / a₀ := div_pos has ha₀
    have hWs : 0 < W s := Real.sqrt_pos.2 hr
    have hW1 : W s ≤ 1 := by
      simp only [hWdef]
      rw [Real.sqrt_le_one, div_le_one ha₀]
      exact hmono hs ⟨htt, le_rfl⟩ hs.2
    have hWv : v₀ ≤ W s := by
      simp only [hWdef, hv₀def]
      exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hmono ⟨le_rfl, htt⟩ hs hs.1) ha₀.le)
    have hW2 : a s = W s ^ 2 * a₀ := by
      simp only [hWdef]; rw [Real.sq_sqrt hr.le]; field_simp
    have hd : HasDerivAt W ((deriv a s / a₀) / (2 * √(a s / a₀))) s :=
      ((hdiff s hs).hasDerivAt.div_const a₀).sqrt hr.ne'
    have hc := ((hG (W s) hWv hW1).comp s hd).div_const (H₀ * a₀)
    have hin := hinn (W s) hWv
    have hHs := hH s hs
    simp only [hubble, redshift] at hHs
    rw [← ha₀def, sqrt_alg Ω a₀ (a s) (W s) hWs ha₀ hW2 hin] at hHs
    have hda : deriv a s = a s * H₀ * (√(Ω + (1 - Ω) * W s ^ 6) / W s ^ 3) := by
      rw [hH₀def]; field_simp at hHs ⊢; linarith [hHs]
    exact hc.congr_deriv
      (deriv_alg H₀ a₀ (a s) (deriv a s) _ (W s) hWs (Real.sqrt_pos.2 hin) ha₀ hH₀ hW2 hda)
  have hint : IntervalIntegrable (fun s => 1 / a s) MeasureTheory.volume t t₀ := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le htt] at hx
    exact (continuousAt_const.div (hdiff x hx).continuousAt (hpos x hx).ne').continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  have hW0 : W t₀ = 1 := by
    show √(a t₀ / a₀) = 1
    rw [← ha₀def, div_self ha₀.ne', Real.sqrt_one]
  have hG1 : G 1 = 0 := by simp [hGdef]
  unfold lumDistFlat comoving
  rw [hftc]
  simp only [hFdef, hW0, hG1]
  rw [intervalIntegral.integral_symm]
  simp only [hGdef, hgdef, hWdef]
  field_simp
  ring

/-- `∫_p^q 2/v³ = 1/p² − 1/q²` for `0 < p ≤ q`. -/
theorem bi_int_cube (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    ∫ v in p..q, 2 / v ^ 3 = 1 / p ^ 2 - 1 / q ^ 2 := by
  have hd : ∀ x ∈ uIcc p q, HasDerivAt (fun v : ℝ => -(1 / v ^ 2)) (2 / x ^ 3) x := by
    intro x hx
    rw [uIcc_of_le hpq] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hp hx.1
    have h := ((hasDerivAt_pow 2 x).inv (pow_pos hx0 2).ne').neg
    convert h using 1
    · ext v; simp [one_div]
    · field_simp; ring
  have hi : IntervalIntegrable (fun v : ℝ => 2 / v ^ 3) MeasureTheory.volume p q := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hpq] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hp hx.1
    exact (continuousAt_const.div (continuousAt_id.pow 3) (pow_pos hx0 3).ne').continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- Pointwise comparison with the empty model for `Ω ≤ 0`: the ratio of the integrand to `2/v³` is
`v³/√(Ω + (1 − Ω)v⁶)`, which decreases in `v`. -/
theorem bi_cmp (Ω v w : ℝ) (hΩ : Ω ≤ 0) (hv : 0 < v) (hvw : v ≤ w)
    (hRv : 0 < Ω + (1 - Ω) * v ^ 6) :
    w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (2 / v ^ 3) ≤ 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  have hw : 0 < w := lt_of_lt_of_le hv hvw
  have h6 : v ^ 6 ≤ w ^ 6 := pow_le_pow_left₀ hv.le hvw 6
  have hRw : 0 < Ω + (1 - Ω) * w ^ 6 := by nlinarith
  have hsv := Real.sqrt_pos.2 hRv
  have hsw := Real.sqrt_pos.2 hRw
  have key : w ^ 3 * √(Ω + (1 - Ω) * v ^ 6) ≤ v ^ 3 * √(Ω + (1 - Ω) * w ^ 6) := by
    rw [show w ^ 3 * √(Ω + (1 - Ω) * v ^ 6) = √(w ^ 6 * (Ω + (1 - Ω) * v ^ 6)) by
          rw [Real.sqrt_mul (by positivity), show w ^ 6 = (w ^ 3) ^ 2 by ring,
            Real.sqrt_sq (by positivity)],
        show v ^ 3 * √(Ω + (1 - Ω) * w ^ 6) = √(v ^ 6 * (Ω + (1 - Ω) * w ^ 6)) by
          rw [Real.sqrt_mul (by positivity), show v ^ 6 = (v ^ 3) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonpos_left h6 hΩ]
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hsv]
  nlinarith [key]

/-- The same comparison above `w`. -/
theorem bi_cmp' (Ω v w : ℝ) (hΩ : Ω ≤ 0) (hw : 0 < w) (hwv : w ≤ v)
    (hRw : 0 < Ω + (1 - Ω) * w ^ 6) :
    2 / √(Ω + (1 - Ω) * v ^ 6) ≤ w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (2 / v ^ 3) := by
  have hv : 0 < v := lt_of_lt_of_le hw hwv
  have h6 : w ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hw.le hwv 6
  have hRv : 0 < Ω + (1 - Ω) * v ^ 6 := by nlinarith
  have hsv := Real.sqrt_pos.2 hRv
  have hsw := Real.sqrt_pos.2 hRw
  have key : v ^ 3 * √(Ω + (1 - Ω) * w ^ 6) ≤ w ^ 3 * √(Ω + (1 - Ω) * v ^ 6) := by
    rw [show w ^ 3 * √(Ω + (1 - Ω) * v ^ 6) = √(w ^ 6 * (Ω + (1 - Ω) * v ^ 6)) by
          rw [Real.sqrt_mul (by positivity), show w ^ 6 = (w ^ 3) ^ 2 by ring,
            Real.sqrt_sq (by positivity)],
        show v ^ 3 * √(Ω + (1 - Ω) * w ^ 6) = √(v ^ 6 * (Ω + (1 - Ω) * w ^ 6)) by
          rw [Real.sqrt_mul (by positivity), show v ^ 6 = (v ^ 3) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonpos_left h6 hΩ]
  rw [div_mul_div_comm, div_le_div_iff₀ hsv (by positivity)]
  nlinarith [key]

theorem bi_cont (Ω p q : ℝ) (hpq : p ≤ q) (hR : ∀ v ∈ Icc p q, 0 < Ω + (1 - Ω) * v ^ 6) :
    IntervalIntegrable (fun v => 2 / √(Ω + (1 - Ω) * v ^ 6)) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [uIcc_of_le hpq] at hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.div
  · exact (by fun_prop : Continuous fun v : ℝ => Ω + (1 - Ω) * v ^ 6).continuousAt.sqrt
  · exact (Real.sqrt_pos.2 (hR x hx)).ne'

/-- Below `w`: `∫_p^w g ≥ r(w) (1/p² − 1/w²)`. -/
theorem bi_lower (Ω p w : ℝ) (hΩ : Ω ≤ 0) (hp : 0 < p) (hpw : p ≤ w)
    (hRp : 0 < Ω + (1 - Ω) * p ^ 6) :
    w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (1 / p ^ 2 - 1 / w ^ 2) ≤
      ∫ v in p..w, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  have hR : ∀ v ∈ Icc p w, 0 < Ω + (1 - Ω) * v ^ 6 := by
    intro v hv
    have : p ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hp.le hv.1 6
    nlinarith
  rw [← bi_int_cube p w hp hpw, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hpw
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hpw] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hp hx.1
    exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.pow 3)
      (pow_pos hx0 3).ne')).continuousWithinAt
  · exact bi_cont Ω p w hpw hR
  · intro v hv
    exact bi_cmp Ω v w hΩ (lt_of_lt_of_le hp hv.1) hv.2 (hR v hv)

/-- Above `w`: `∫_w^1 g ≤ r(w) (1/w² − 1)`. -/
theorem bi_upper (Ω w : ℝ) (hΩ : Ω ≤ 0) (hw : 0 < w) (hw1 : w ≤ 1)
    (hRw : 0 < Ω + (1 - Ω) * w ^ 6) :
    ∫ v in w..1, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤
      w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (1 / w ^ 2 - 1 / 1 ^ 2) := by
  have hR : ∀ v ∈ Icc w 1, 0 < Ω + (1 - Ω) * v ^ 6 := by
    intro v hv
    have : w ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hw.le hv.1 6
    nlinarith
  rw [← bi_int_cube w 1 hw hw1, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hw1
  · exact bi_cont Ω w 1 hw1 hR
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hw1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hw hx.1
    exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.pow 3)
      (pow_pos hx0 3).ne')).continuousWithinAt
  · intro v hv
    exact bi_cmp' Ω v w hΩ hw hv.1 hRw

/-- For a negative density the distance to the source at `1 + z = 4√2` is at least `284/100` times the
distance to the source at `1 + z = 2√2` (the bound `delta_ge` uses for `0 ≤ Ω ≤ 1`). -/
theorem bi_ratio (Ω : ℝ) (hΩ : Ω < 0)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1) :
    0 < lumDistFlat a t₀ t₃ ∧ 284 / 100 * lumDistFlat a t₀ t₃ ≤ lumDistFlat a t₀ t₅ := by
  have h₅₀ : t₅ ≤ t₀ := le_trans h₅₃ h₃₀
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₅₃, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  obtain ⟨hq2l, hq2u⟩ := Checked.Cosmography.B1Fit.sqrt2_bounds
  have hq2s : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr3 := ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃
  have hr5 := ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅
  rw [show (1:ℝ) + (2 * √2 - 1) = 2 * √2 by ring] at hr3
  rw [show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring] at hr5
  rcases le_or_gt Ω (-1 / 63) with hlo | hhi
  · exfalso
    apply bi_unreach Ω a t₅ t₀ h₅₀ hpos hdiff hH
    rw [hz₅, show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring]
    have e : (4 * √2) ^ 3 = 128 * √2 := by
      rw [mul_pow, show √2 ^ 3 = √2 ^ 2 * √2 by ring, hq2s]; ring
    rw [e]
    nlinarith
  have hsub : ∀ u, t₅ ≤ u → Set.Icc u t₀ ⊆ Set.Icc t₅ t₀ := fun u hu => Set.Icc_subset_Icc_left hu
  -- a time between the two sources with a = a₀ / 4
  have hcont : ContinuousOn a (Set.Icc t₅ t₃) := fun x hx =>
    (hdiff x ⟨hx.1, le_trans hx.2 h₃₀⟩).continuousAt.continuousWithinAt
  have e5 : a t₅ = a t₀ / (4 * √2) := by
    field_simp at hr5 ⊢; linarith
  have e3 : a t₃ = a t₀ / (2 * √2) := by
    field_simp at hr3 ⊢; linarith
  have hin : a t₀ / 4 ∈ Set.Icc (a t₅) (a t₃) := by
    rw [e5, e3]
    constructor
    · exact div_le_div_of_nonneg_left ha₀.le (by norm_num) (by nlinarith)
    · exact div_le_div_of_nonneg_left ha₀.le (by positivity) (by nlinarith)
  obtain ⟨s, hs, has⟩ := intermediate_value_Icc h₅₃ hcont hin
  have hs₀ : s ≤ t₀ := le_trans hs.2 h₃₀
  have has0 : a s / a t₀ = 1 / 4 := by rw [has]; field_simp
  have hhalf : √(a s / a t₀) = 1 / 2 := by
    rw [has0, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  set w := √(1 / (2 * √2)) with hwdef
  have hw2 : w ^ 2 = 1 / (2 * √2) := Real.sq_sqrt (by positivity)
  have hw0 : 0 < w := Real.sqrt_pos.2 (by positivity)
  have hwh : 1 / 2 ≤ w := by
    rw [hwdef]; apply Real.le_sqrt_of_sq_le
    rw [div_pow, one_pow, one_div_le_one_div (by norm_num) (by positivity)]; nlinarith
  have hw1 : w ≤ 1 := by
    rw [hwdef, Real.sqrt_le_one]
    rw [div_le_one (by positivity)]; nlinarith
  have hiw : 1 / w ^ 2 = 2 * √2 := by rw [hw2]; field_simp
  have hR : ∀ y, 1 / 2 ≤ y → 0 < Ω + (1 - Ω) * y ^ 6 := by
    intro y hy
    have : (1 / 2 : ℝ) ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ (by norm_num) hy 6
    nlinarith
  -- the two bridges
  have hbs := bi_bridge Ω (by linarith) a s t₀ hs₀ (fun u hu => hpos u (hsub s hs.1 hu))
    (fun u hu => hdiff u (hsub s hs.1 hu)) hH₀ (fun u hu => hH u (hsub s hs.1 hu))
    (by rw [hhalf]; exact hR _ le_rfl)
  have h3w : √(a t₃ / a t₀) = w := by rw [hr3]
  have hb3 := bi_bridge Ω (by linarith) a t₃ t₀ h₃₀ (fun u hu => hpos u (hsub t₃ h₅₃ hu))
    (fun u hu => hdiff u (hsub t₃ h₅₃ hu)) hH₀ (fun u hu => hH u (hsub t₃ h₅₃ hu))
    (by rw [h3w]; exact hR _ hwh)
  rw [hhalf] at hbs
  rw [h3w] at hb3
  have hzs : 1 + redshift a t₀ s = 4 := by
    unfold redshift; rw [has]; field_simp; ring
  rw [hzs] at hbs
  rw [hz₃, show (1:ℝ) + (2 * √2 - 1) = 2 * √2 by ring] at hb3
  set g : ℝ → ℝ := fun v => 2 / √(Ω + (1 - Ω) * v ^ 6) with hgdef
  set A := ∫ v in (1 / 2 : ℝ)..w, g v with hA
  set B := ∫ v in w..1, g v with hB
  have hsplit : (∫ v in (1 / 2 : ℝ)..1, g v) = A + B :=
    (intervalIntegral.integral_add_adjacent_intervals
      (bi_cont Ω _ _ hwh (fun y hy => hR y hy.1))
      (bi_cont Ω _ _ hw1 (fun y hy => hR y (le_trans hwh hy.1)))).symm
  rw [hsplit] at hbs
  have hlow := bi_lower Ω (1 / 2) w hΩ.le (by norm_num) hwh (hR _ le_rfl)
  have hupp := bi_upper Ω w hΩ.le hw0 hw1 (hR _ hwh)
  rw [hiw] at hlow hupp
  rw [show (1:ℝ) / (1 / 2) ^ 2 = 4 by norm_num] at hlow
  rw [show (1:ℝ) / 1 ^ 2 = 1 by norm_num] at hupp
  set r := w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) with hr
  have hrp : 0 < r := div_pos (pow_pos hw0 3) (Real.sqrt_pos.2 (hR _ hwh))
  have hBp : 0 < B := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (bi_cont Ω _ _ hw1 (fun y hy => hR y (le_trans hwh hy.1)))
    · intro y hy
      exact div_pos (by norm_num) (Real.sqrt_pos.2 (hR y (le_trans hwh hy.1.le)))
    · rcases eq_or_lt_of_le hw1 with h | h
      · exfalso; rw [h, one_pow, eq_div_iff (by positivity)] at hw2; nlinarith
      · exact h
  -- (2√2 − 1)(A + B) ≥ 3B
  have hlow' : r * (4 - 2 * √2) ≤ A := hlow
  have hupp' : B ≤ r * (2 * √2 - 1) := hupp
  have h42 : 0 ≤ 4 - 2 * √2 := by linarith
  have h21 : 0 ≤ 2 * √2 - 1 := by linarith
  have hk : 3 * B ≤ (2 * √2 - 1) * (A + B) := by
    have h1 := mul_le_mul_of_nonneg_left hupp' h42
    have h2 := mul_le_mul_of_nonneg_left hlow' h21
    linear_combination h1 + h2
  have hA0 : 0 < A := lt_of_lt_of_le (mul_pos hrp (by linarith)) hlow'
  -- the farther source is at least √2 times the time with a = a₀/4
  have hcom : comoving a t₀ s ≤ comoving a t₀ t₅ := by
    unfold comoving
    have hc : ContinuousOn (fun u => 1 / a u) (Set.Icc t₅ t₀) := fun x hx =>
      (continuousAt_const.div (hdiff x hx).continuousAt (hpos x hx).ne').continuousWithinAt
    have hi1 : IntervalIntegrable (fun u => 1 / a u) MeasureTheory.volume t₅ s :=
      (hc.mono (Set.Icc_subset_Icc_right hs₀)).intervalIntegrable_of_Icc hs.1
    have hi2 : IntervalIntegrable (fun u => 1 / a u) MeasureTheory.volume s t₀ :=
      (hc.mono (hsub s hs.1)).intervalIntegrable_of_Icc hs₀
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have : 0 ≤ ∫ u in t₅..s, 1 / a u :=
      intervalIntegral.integral_nonneg hs.1 (fun u hu =>
        (div_pos one_pos (hpos u ⟨hu.1, le_trans hu.2 hs₀⟩)).le)
    linarith
  have hD5 : √2 * lumDistFlat a t₀ s ≤ lumDistFlat a t₀ t₅ := by
    unfold lumDistFlat
    rw [hzs, hz₅, show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring]
    have : 0 ≤ comoving a t₀ s := by
      unfold comoving
      exact intervalIntegral.integral_nonneg hs₀ (fun u hu =>
        (div_pos one_pos (hpos u ⟨le_trans hs.1 hu.1, hu.2⟩)).le)
    calc √2 * (a t₀ * 4 * comoving a t₀ s) = a t₀ * (4 * √2) * comoving a t₀ s := by ring
      _ ≤ a t₀ * (4 * √2) * comoving a t₀ t₅ := mul_le_mul_of_nonneg_left hcom (by positivity)
  have hH0p := hH₀
  rw [hbs] at hD5
  rw [hb3]
  refine ⟨by positivity, ?_⟩
  have hfin : 284 / 100 * (2 * √2 / hubble a t₀ * B) ≤ √2 * (4 / hubble a t₀ * (A + B)) := by
    rw [show 284 / 100 * (2 * √2 / hubble a t₀ * B) = √2 / hubble a t₀ * (568 / 100 * B) by ring,
      show √2 * (4 / hubble a t₀ * (A + B)) = √2 / hubble a t₀ * (4 * (A + B)) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h3 : (2 * √2 - 1) * (A + B) ≤ (2 * (141421357 / 100000000) - 1) * (A + B) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  linarith

/-- `delta_ge` for a negative density. -/
lemma bi_delta (Ω : ℝ) (hΩ : Ω < 0)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H) (x₃ x₅ : ℝ)
    (hx₃ : Real.logb 10 (1 + (2 * √2 - 1)) = x₃) (hx₅ : Real.logb 10 (1 + (4 * √2 - 1)) = x₅)
    (hQ3 : 0 < x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
    (hQ5 : 0 < x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4) :
    5 * Real.logb 10 (284 / 100 * (x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
        / (x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4))
      ≤ 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅))
        - 5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃)) := by
  obtain ⟨hD3, hD⟩ := bi_ratio Ω hΩ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅
  set D3 := lumDistFlat a t₀ t₃ with hD3def
  set D5 := lumDistFlat a t₀ t₅ with hD5def
  have hD5 : 0 < D5 := by linarith
  set Q3 := x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4 with hQ3def
  set Q5 := x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4 with hQ5def
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [hz₃, hz₅, lp4_eq a₂ a₃ a₄ H x₃ _ hx₃, lp4_eq a₂ a₃ a₄ H x₅ _ hx₅]
  have hX3 : 0 < D3 / (Real.log 10 / H * Q3) := by positivity
  have hX5 : 0 < D5 / (Real.log 10 / H * Q5) := by positivity
  have e : 5 * Real.logb 10 (D5 / (Real.log 10 / H * Q5))
      - 5 * Real.logb 10 (D3 / (Real.log 10 / H * Q3))
      = 5 * Real.logb 10 ((D5 / (Real.log 10 / H * Q5)) / (D3 / (Real.log 10 / H * Q3))) := by
    rw [Real.logb_div hX5.ne' hX3.ne']; ring
  have key : (D5 / (Real.log 10 / H * Q5)) / (D3 / (Real.log 10 / H * Q3))
      = D5 / D3 * (Q3 / Q5) := by
    field_simp
  rw [e, key]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  rw [show 284 / 100 * Q3 / Q5 = 284 / 100 * (Q3 / Q5) by ring]
  exact mul_le_mul_of_nonneg_right (by rw [le_div_iff₀ hD3]; linarith) (by positivity)

/-- Without `0 ≤ Ω`: a negative density either cannot reach the farther source (`bi_unreach`) or keeps the
distance ratio above the bound of `delta_ge` (`bi_delta`). -/
theorem l19_sq_central_r1 : dropped% Checked.Cosmography.B1L19.l19_sq_central 1 := by
  intro Ω hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ H hHp
  rcases le_or_gt 0 Ω with h0 | hneg
  · exact l19_sq_central Ω h0 hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ H hHp
  · obtain ⟨hL1, hL2⟩ := L_bounds
    obtain ⟨hQ5, hF⟩ := poly_sq_central _ hL1 hL2
    have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
    have hd := bi_delta Ω hneg a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ 3.075 4.466 (-3.716) H hHp
      _ _ x3_eq x5_eq hQ3 hQ5
    have hq : (1.175 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
        + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
        / (5 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + 4.466 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + (-3.716) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
      rw [lt_div_iff₀ hQ5]; linarith
    have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
    have := logb_1175
    linarith

/-- Without `0 ≤ Ω`: a negative density either cannot reach the farther source (`bi_unreach`) or keeps the
distance ratio above the bound of `delta_ge` (`bi_delta`). -/
theorem l19_sqg_central_r1 : dropped% Checked.Cosmography.B1L19.l19_sqg_central 1 := by
  intro Ω hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ H hHp
  rcases le_or_gt 0 Ω with h0 | hneg
  · exact l19_sqg_central Ω h0 hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ H hHp
  · obtain ⟨hL1, hL2⟩ := L_bounds
    obtain ⟨hQ5, hF⟩ := poly_sqg_central _ hL1 hL2
    have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
    have hd := bi_delta Ω hneg a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ 3.205 3.564 (-2.510) H hHp
      _ _ x3_eq x5_eq hQ3 hQ5
    have hq : (1.149 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
        + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
        / (5 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + 3.564 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + (-2.510) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
      rw [lt_div_iff₀ hQ5]; linarith
    have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
    have := logb_1149
    linarith

/-- Without `0 ≤ Ω`: a negative density either cannot reach the farther source (`bi_unreach`) or keeps the
distance ratio above the bound of `delta_ge` (`bi_delta`). -/
theorem l19_sq_box_r1 : dropped% Checked.Cosmography.B1L19.l19_sq_box 1 := by
  intro Ω hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp₅
  rcases le_or_gt 0 Ω with h0 | hneg
  · exact l19_sq_box Ω h0 hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp₅
  · obtain ⟨hL1, hL2⟩ := L_bounds
    rw [hz₅, lp4_eq a₂ a₃ a₄ H _ _ x5_eq] at hp₅
    have hQ5 := (mul_pos_iff_of_pos_left (div_pos (Real.log_pos (by norm_num)) hHp)).1 hp₅
    have hF := poly_box _ a₂ a₃ a₄ 2.906 5.479 (-1.794) hL1 hL2 ha₂ ha₃ ha₄ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
    have hd := bi_delta Ω hneg a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp
      _ _ x3_eq x5_eq hQ3 hQ5
    have hq : (1 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
        + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
        / (5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
      rw [lt_div_iff₀ hQ5]; linarith
    have hlg := Real.logb_pos (by norm_num : (1:ℝ) < 10) hq
    linarith

/-- Without `0 ≤ Ω`: a negative density either cannot reach the farther source (`bi_unreach`) or keeps the
distance ratio above the bound of `delta_ge` (`bi_delta`). -/
theorem l19_sqg_box_r1 : dropped% Checked.Cosmography.B1L19.l19_sqg_box 1 := by
  intro Ω hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp₅
  rcases le_or_gt 0 Ω with h0 | hneg
  · exact l19_sqg_box Ω h0 hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp₅
  · obtain ⟨hL1, hL2⟩ := L_bounds
    rw [hz₅, lp4_eq a₂ a₃ a₄ H _ _ x5_eq] at hp₅
    have hQ5 := (mul_pos_iff_of_pos_left (div_pos (Real.log_pos (by norm_num)) hHp)).1 hp₅
    have hF := poly_box _ a₂ a₃ a₄ 3.043 4.480 (-0.915) hL1 hL2 ha₂ ha₃ ha₄ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
    have hd := bi_delta Ω hneg a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp
      _ _ x3_eq x5_eq hQ3 hQ5
    have hq : (1 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
        + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
        / (5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
      rw [lt_div_iff₀ hQ5]; linarith
    have hlg := Real.logb_pos (by norm_num : (1:ℝ) < 10) hq
    linarith

end Checked.Trust.NCBI
