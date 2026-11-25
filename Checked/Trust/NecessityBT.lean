import Checked.Trust.NecessityBI
import Checked.Cosmography.B1FitRL19

/-!
# Hypothesis necessity, the RL19 box: the upper density bound (trust track T2b)

Run 2026-11-25T0628Z. `B1FitRL19.rl19_box_unmatched` assumes that the density parameter of its flat model is at most
one. That hypothesis is REDUNDANT (`rl19_box_unmatched_r2`): for every density above one the nearest and the middle
source alone already forbid the match, with no certified integral.

* **The distance above density one** (`bt_bridge`): the luminosity distance is the same integral as below one; the
  radicand of the integrand is at least one between the source and the present, so no lower bound on the density is
  needed for the change of variables.
* **The integrand increases** (`bt_mono`) above density one, so the distance to the nearest source is at least the
  fraction of the distance to the middle source that a constant integrand gives (`bt_ratio13`; the mirror image of
  `NCBL.bl_ratio13`, which is the other inequality below density one).
* **The residuals** at the nearest and the middle source bound the ratio of the two distances from above by the
  ratio of the cubic's values (`B1Fit.ratio_step`, `B1Fit.ratio_clean`); inside the box of coefficients that bound is
  about five percent below the lower bound of the previous item (`bt_core`), a contradiction.

The float scan `runs/2026-11-25T0628Z/scripts/scan_h2.py` (the magnitude spread at the best corner of the box, for
densities from one to a million) shows the nearest-to-middle residual difference never falls below eighteen hundredths
of a magnitude above density one, where the statement allows one tenth.
-/

namespace Checked.Trust.NCBT

open Set
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1Fit
open Checked.Trust.NCBI

/-- Above density one the radicand is at least one on `[0, 1]`. -/
theorem bt_inner (Ω v : ℝ) (h1 : 1 ≤ Ω) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < Ω + (1 - Ω) * v ^ 6 := by
  have h6 : v ^ 6 ≤ 1 := pow_le_one₀ hv0 hv1
  nlinarith [mul_le_mul_of_nonneg_left h6 (sub_nonneg.2 h1)]

/-- The bridge above density one: the luminosity distance is `(1 + z)/H₀` times the integral of the integrand of
the law from `√(a(t)/a(t₀))` to one. -/
theorem bt_bridge0 (Ω : ℝ) (h1 : 1 ≤ Ω)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    lumDistFlat a t₀ t = (1 + redshift a t₀ t) / hubble a t₀ *
      ∫ v in √(a t / a t₀)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  have hmono := bi_mono Ω a t t₀ hpos hdiff hH₀ hH
  set a₀ := a t₀ with ha₀def
  set H₀ := hubble a t₀ with hH₀def
  have ha₀ : 0 < a₀ := hpos t₀ ⟨htt, le_rfl⟩
  set v₀ := √(a t / a₀) with hv₀def
  have hv₀ : 0 < v₀ := Real.sqrt_pos.2 (div_pos (hpos t ⟨le_rfl, htt⟩) ha₀)
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
      have hy0 : 0 < y := lt_of_lt_of_le hv₀ (le_trans hx hy.1)
      exact ⟨hy0, bt_inner Ω y h1 hy0.le hy.2⟩
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
    have hin := bt_inner Ω (W s) h1 hWs.le hW1
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

/-- The bridge at one source, in the form of `NCBL.bl_bridge`: the distance is `S/H₀` times the integral from
`√(1/S)`. -/
theorem bt_bridge (Ω : ℝ) (h1 : 1 ≤ Ω) (a : ℝ → ℝ) (t₅ t t₀ : ℝ) (h5 : t₅ ≤ t) (ht : t ≤ t₀)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hdiff : ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (S : ℝ) (hz : redshift a t₀ t = S - 1) :
    lumDistFlat a t₀ t = S / hubble a t₀ * ∫ v in √(1 / S)..1, gL Ω v := by
  have hsub : Icc t t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h5
  have hbr := bt_bridge0 Ω h1 a t t₀ ht (fun s hs => hpos s (hsub hs))
    (fun s hs => hdiff s (hsub hs)) hH₀ (fun s hs => hH s (hsub hs))
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h5.trans ht, le_rfl⟩
  have ha : 0 < a t := hpos t ⟨h5, ht⟩
  have es : (1:ℝ) + (S - 1) = S := by ring
  rw [ratio_of_z a t t₀ _ ha ha₀ hz, es, hz, es] at hbr
  exact hbr

/-- Above density one the integrand increases on `(0, 1]`. -/
theorem bt_mono (Ω v w : ℝ) (h1 : 1 ≤ Ω) (hv : 0 < v) (hvw : v ≤ w) (hw1 : w ≤ 1) :
    gL Ω v ≤ gL Ω w := by
  have hw : 0 < w := lt_of_lt_of_le hv hvw
  have hRw := bt_inner Ω w h1 hw.le hw1
  have h6 : v ^ 6 ≤ w ^ 6 := pow_le_pow_left₀ hv.le hvw 6
  unfold gL
  apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hRw)
  apply Real.sqrt_le_sqrt
  nlinarith [mul_le_mul_of_nonneg_left h6 (sub_nonneg.2 h1)]

theorem bt_int (Ω p q : ℝ) (h1 : 1 ≤ Ω) (hp : 0 < p) (hpq : p ≤ q) (hq : q ≤ 1) :
    IntervalIntegrable (gL Ω) MeasureTheory.volume p q :=
  bi_cont Ω p q hpq (fun v hv => bt_inner Ω v h1 (hp.le.trans hv.1) (hv.2.trans hq))

theorem bt_Jpos (Ω w : ℝ) (h1 : 1 ≤ Ω) (hw : 0 < w) (hw1 : w < 1) : 0 < ∫ v in w..1, gL Ω v := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (bt_int Ω w 1 h1 hw hw1.le le_rfl) _ hw1
  intro v hv
  unfold gL
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (bt_inner Ω v h1 (hw.le.trans hv.1.le) hv.2.le))

/-- Above density one the distance integral to the middle source is at most `(1 − w₃)/(1 − w₁)` times the one to
the nearest source (the integrand increases). -/
theorem bt_ratio13 (Ω : ℝ) (h1 : 1 ≤ Ω) :
    (1 - √(1 / √2)) * ∫ v in √(1 / (2 * √2))..1, gL Ω v ≤
      (1 - √(1 / (2 * √2))) * ∫ v in √(1 / √2)..1, gL Ω v := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  set w1 := √(1 / √2) with hw1
  set w3 := √(1 / (2 * √2)) with hw3
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  have h31 : w3 ≤ w1 := by
    rw [hw1, hw3]; apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le hq; linarith
  have hsplit : ∫ v in w3..1, gL Ω v = (∫ v in w3..w1, gL Ω v) + ∫ v in w1..1, gL Ω v :=
    (intervalIntegral.integral_add_adjacent_intervals (bt_int Ω _ _ h1 hw3p h31 hw11.le)
      (bt_int Ω _ _ h1 hw1p hw11.le le_rfl)).symm
  -- above w₁ the integrand is at least its value at w₁, below at most
  have hA : ∫ v in w1..1, gL Ω w1 ≤ ∫ v in w1..1, gL Ω v := by
    apply intervalIntegral.integral_mono_on hw11.le intervalIntegrable_const
      (bt_int Ω _ _ h1 hw1p hw11.le le_rfl)
    intro v hv
    exact bt_mono Ω w1 v h1 hw1p hv.1 hv.2
  have hB : ∫ v in w3..w1, gL Ω v ≤ ∫ v in w3..w1, gL Ω w1 := by
    apply intervalIntegral.integral_mono_on h31 (bt_int Ω _ _ h1 hw3p h31 hw11.le)
      intervalIntegrable_const
    intro v hv
    exact bt_mono Ω v w1 h1 (lt_of_lt_of_le hw3p hv.1) hv.2 hw11.le
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
  rw [hsplit]
  have hg : 0 ≤ gL Ω w1 := gL_nonneg Ω w1
  nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ w1 - w3),
    mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ 1 - w1)]

/-- Bounds of the two lower limits: `2^(-1/4)` and `2^(-3/4)`. -/
theorem bt_w1 : √(1 / √2) ≤ 841 / 1000 := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  exact (wb (√2) (841 / 1000) (8408 / 10000) (by linarith) (by norm_num)
    (by nlinarith) (by nlinarith)).2

theorem bt_w3 : 5946 / 10000 ≤ √(1 / (2 * √2)) := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  exact (wb (2 * √2) (5947 / 10000) (5946 / 10000) (by linarith) (by norm_num)
    (by nlinarith) (by nlinarith)).1

/-- The cubic's values at the nearest and the middle source, against the two lower limits: inside the box the
middle value exceeds `2(1 − w₃)/(κ(1 − w₁))` times the nearest one. -/
theorem bt_core (ℓ L a₂ a₃ w1 w3 : ℝ) (hℓ : 0 < ℓ) (hL : 0 < L) (hy : 30101 / 100000 ≤ ℓ / L)
    (ha₂ : 343 / 100 ≤ a₂) (ha₃ : 157 / 100 ≤ a₃) (hw1 : w1 ≤ 841 / 1000) (hw3 : 5946 / 10000 ≤ w3) :
    2 * (1 - w3) * (1 * ℓ / 2 + a₂ / L * (1 * ℓ / 2) ^ 2 + a₃ / L ^ 2 * (1 * ℓ / 2) ^ 3) <
      95499 / 100000 * (1 - w1) *
        (3 * ℓ / 2 + a₂ / L * (3 * ℓ / 2) ^ 2 + a₃ / L ^ 2 * (3 * ℓ / 2) ^ 3) := by
  set y := ℓ / L with hydef
  have e1 : 1 * ℓ / 2 + a₂ / L * (1 * ℓ / 2) ^ 2 + a₃ / L ^ 2 * (1 * ℓ / 2) ^ 3 =
      ℓ / 2 * (1 + a₂ * y / 2 + a₃ * y ^ 2 / 4) := by
    rw [hydef]; field_simp; ring
  have e3 : 3 * ℓ / 2 + a₂ / L * (3 * ℓ / 2) ^ 2 + a₃ / L ^ 2 * (3 * ℓ / 2) ^ 3 =
      ℓ / 2 * (3 * (1 + 3 * a₂ * y / 2 + 9 * a₃ * y ^ 2 / 4)) := by
    rw [hydef]; field_simp; ring
  rw [e1, e3]
  set A := 95499 / 100000 * (1 - w1) with hA
  set B := 2 * (1 - w3) with hB
  have hAl : 15184 / 100000 ≤ A := by rw [hA]; nlinarith
  have hBu : B ≤ 8108 / 10000 := by rw [hB]; linarith
  set p := a₂ * y / 2 with hp
  set q := a₃ * y ^ 2 / 4 with hq
  have hy0 : 0 ≤ y := by linarith
  have hpl : 516232 / 1000000 ≤ p := by
    rw [hp]; nlinarith [mul_le_mul ha₂ hy (by norm_num) (by linarith : (0:ℝ) ≤ a₂)]
  have hy2 : (30101 / 100000) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hy 2
  have hql : 35563 / 1000000 ≤ q := by
    rw [hq]; nlinarith [mul_le_mul ha₃ hy2 (by norm_num) (by linarith : (0:ℝ) ≤ a₃)]
  have h9 : 0 ≤ 9 * A - B := by linarith
  have h27 : 0 ≤ 27 * A - B := by linarith
  have key : 0 < (3 * A - B) + p * (9 * A - B) + q * (27 * A - B) := by
    nlinarith [mul_le_mul_of_nonneg_right hpl h9, mul_le_mul_of_nonneg_right hql h27]
  have hℓ2 : 0 < ℓ / 2 := by positivity
  have : B * (ℓ / 2 * (1 + p + q)) < A * (ℓ / 2 * (3 * (1 + 3 * p + 9 * q))) := by
    have := mul_pos hℓ2 key
    nlinarith [this]
  have e1' : a₂ * y / 2 = p := rfl
  have e3' : 3 * a₂ * y / 2 = 3 * p := by rw [hp]; ring
  have e9 : 9 * a₃ * y ^ 2 / 4 = 9 * q := by rw [hq]; ring
  rw [e3', e9]
  linarith

open Checked.Cosmography.B1FitRL19 in
/-- Without `Ω ≤ 1`: for a density above one the nearest and the middle source alone forbid the match (the
integrand increases, `bt_ratio13`; the box makes the cubic's middle value too large, `bt_core`). -/
theorem rl19_box_unmatched_r2 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 2 := by
  intro Ω h0 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp
    hp1 hp3 hp5
  rcases le_or_gt Ω 1 with h1 | h1
  · exact Checked.Cosmography.B1FitRL19.rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
      hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp hp1 hp3 hp5
  rintro ⟨hm1, hm3, -⟩
  have h1' : 1 ≤ Ω := h1.le
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb1 := bt_bridge Ω h1' a t₅ t₁ t₀ (h53.trans h31) h10 hpos hdiff hH₀ hH (√2) hz1
  have hb3 := bt_bridge Ω h1' a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  have hJ1 : 0 < ∫ v in √(1 / √2)..1, gL Ω v := bt_Jpos Ω _ h1' hw1p hw11
  have hJ3 : 0 < ∫ v in √(1 / (2 * √2))..1, gL Ω v := bt_Jpos Ω _ h1' hw3p hw31
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hb1]; positivity
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hb3]; positivity
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have hL0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have h := ratio_step _ _ _ _ c hd3 hd1 hp3 hp1 hm3 hm1
  rw [hb1, hb3, hz1, hz3, hL1, hL3] at h
  rw [hz1, hL1] at hp1
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  set P1 := 1 * ℓ / 2 + a₂ / Real.log 10 * (1 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (1 * ℓ / 2) ^ 3
  set P3 := 3 * ℓ / 2 + a₂ / Real.log 10 * (3 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (3 * ℓ / 2) ^ 3
  have hP1 : 0 < P1 := (div_pos_iff_of_pos_right hHp).1 hp1
  have r := ratio_clean _ (√2) (2 * √2) _ H J1 J3 P3 P1 2 hq hH₀ hHp (by ring) h
  have hρ := bt_ratio13 Ω h1'
  set w1 := √(1 / √2) with hw1
  set w3 := √(1 / (2 * √2)) with hw3
  have hw1u := bt_w1
  have hw3l := bt_w3
  have hlt := bt_core ℓ (Real.log 10) a₂ a₃ w1 w3 hℓ0 hL0 (Checked.Cosmography.B1FitWitness.t_bounds).1
    h2l h3l hw1u hw3l
  -- κ (1 − w₁) J₁ P₃ ≤ 2 (1 − w₁) J₃ P₁ ≤ 2 (1 − w₃) J₁ P₁
  have s1 : 95499 / 100000 * (1 - w1) * P3 * J1 ≤ 2 * (1 - w1) * J3 * P1 := by
    have := mul_le_mul_of_nonneg_left r (by linarith : (0:ℝ) ≤ 1 - w1)
    linarith only [this]
  have s2 : 2 * (1 - w1) * J3 * P1 ≤ 2 * (1 - w3) * P1 * J1 := by
    have := mul_le_mul_of_nonneg_left hρ (by linarith : (0:ℝ) ≤ 2 * P1)
    linarith only [this]
  have s3 : 2 * (1 - w3) * P1 * J1 < 95499 / 100000 * (1 - w1) * P3 * J1 :=
    mul_lt_mul_of_pos_right hlt hJ1
  linarith only [s1, s2, s3]

end Checked.Trust.NCBT
