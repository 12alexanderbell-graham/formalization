import Checked.Trust.NecessityBK

/-!
# Hypothesis necessity, the fit-direction headline: the positive normalisation and the positivity of the polynomial at the three sources (trust track T2b)

Run 2026-11-21T0828Z. `B1Fit.fit_direction` assumes a positive normalisation of the cubic log-polynomial distance
and that this distance is positive at each of its three sources. Each of these four hypotheses is REDUNDANT (one at a
time): at the nearest and the farthest source and for the normalisation the other hypotheses force the sign, and
at the middle source a value that is not positive gives the direction outright.

* **The cubic's values satisfy one linear relation** (`bl_rel`): a cubic through the origin with slope one, read at
  one, three and five halves of `log 2`, has thirty times its first value, minus twenty thirds of its second, plus
  six fifths of its third equal to eight times `log 2` (the third divided difference of a quadratic vanishes).
* **Distance ratios without certified integrals.** For a density between zero and one the integrand of the
  distance divided by that of the empty model increases (`bl_cmp`, `bl_cmp'`), so the ratio of the distances to
  the farthest and the middle source is at most the empty model's (`bl_ratio53`); the integrand decreases
  (`gL_anti`), so the ratio of the distances to the nearest and the middle source is at most the ratio for a
  constant integrand (`bl_ratio13`).
* **Nearest source** (`fit_direction_r14`): if the value there is not positive, the relation makes the farthest
  value exceed fifty ninths of the middle one, while the two residuals there allow at most about five and one
  third.
* **Farthest source** (`fit_direction_r16`): if the value there is not positive, the relation makes the nearest
  value exceed two ninths of the middle one, while the two residuals there allow at most about one fifth.
* **Normalisation** (`fit_direction_r13`): a zero normalisation makes the polynomial distance zero; a negative one
  makes all three values negative, and then the relation asks the middle value to exceed a combination of the
  other two that the residuals forbid (`bl_comb`: a lower bound of the nearest and farthest distance integrals by
  the middle one, from the two monotonicities above and a case split on the integrand at the middle source).
* **Middle source** (`fit_direction_r15`): if the value there is not positive while the other two are, the
  quadratic factor of the cubic is convex and dips below zero between the nearest and the farthest source; with
  the ratio of the farthest to the nearest value that the residuals allow (`bl_ratio15`, the integrand
  decreases), its curvature is so large that the conclusion holds with a margin of about two in the rescaled
  coefficients, where it needs about one tenth.
-/

namespace Checked.Trust.NCBL

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1Fit Set
open Checked.Trust.NCBI

/-- For a density between zero and one, below `w` the integrand is at most `r(w)` times the empty model's. -/
theorem bl_cmp (Ω v w : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (hv : 0 < v) (hvw : v ≤ w) :
    2 / √(Ω + (1 - Ω) * v ^ 6) ≤ w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (2 / v ^ 3) := by
  have hw : 0 < w := lt_of_lt_of_le hv hvw
  have h6 : v ^ 6 ≤ w ^ 6 := pow_le_pow_left₀ hv.le hvw 6
  have hRv := inner_pos Ω v h0 h1 hv
  have hRw := inner_pos Ω w h0 h1 hw
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
    nlinarith [mul_le_mul_of_nonneg_left h6 h0]
  rw [div_mul_div_comm, div_le_div_iff₀ hsv (by positivity)]
  nlinarith [key]

/-- The same comparison above `w`, the other way. -/
theorem bl_cmp' (Ω v w : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (hw : 0 < w) (hwv : w ≤ v) :
    w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (2 / v ^ 3) ≤ 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  have hv : 0 < v := lt_of_lt_of_le hw hwv
  have h6 : w ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hw.le hwv 6
  have hRv := inner_pos Ω v h0 h1 hv
  have hRw := inner_pos Ω w h0 h1 hw
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
    nlinarith [mul_le_mul_of_nonneg_left h6 h0]
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hsv]
  nlinarith [key]

theorem bl_cube_int (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) (c : ℝ) :
    IntervalIntegrable (fun v : ℝ => c * (2 / v ^ 3)) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [uIcc_of_le hpq] at hx
  have hx0 : 0 < x := lt_of_lt_of_le hp hx.1
  exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.pow 3)
    (pow_pos hx0 3).ne')).continuousWithinAt

/-- Below `w`: `∫_p^w g ≤ r(w) (1/p² − 1/w²)`. -/
theorem bl_upper (Ω p w : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (hp : 0 < p) (hpw : p ≤ w) :
    ∫ v in p..w, gL Ω v ≤ w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (1 / p ^ 2 - 1 / w ^ 2) := by
  rw [← bi_int_cube p w hp hpw, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hpw (gL_intInt Ω h0 h1 p w hp hpw) (bl_cube_int p w hp hpw _)
  intro v hv
  exact bl_cmp Ω v w h0 h1 (lt_of_lt_of_le hp hv.1) hv.2

/-- Above `w`: `∫_w^1 g ≥ r(w) (1/w² − 1)`. -/
theorem bl_lower (Ω w : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (hw : 0 < w) (hw1 : w ≤ 1) :
    w ^ 3 / √(Ω + (1 - Ω) * w ^ 6) * (1 / w ^ 2 - 1 / 1 ^ 2) ≤ ∫ v in w..1, gL Ω v := by
  rw [← bi_int_cube w 1 hw hw1, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hw1 (bl_cube_int w 1 hw hw1 _) (gL_intInt Ω h0 h1 w 1 hw hw1)
  intro v hv
  exact bl_cmp' Ω v w h0 h1 hw hv.1

/-- The distance integral to the farthest source is at most `(4√2 − 1)/(2√2 − 1)` times the one to the
middle source (the empty model's ratio). -/
theorem bl_ratio53 (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (2 * √2 - 1) * ∫ v in √(1 / (4 * √2))..1, gL Ω v ≤
      (4 * √2 - 1) * ∫ v in √(1 / (2 * √2))..1, gL Ω v := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  set w5 := √(1 / (4 * √2)) with hw5
  set w3 := √(1 / (2 * √2)) with hw3
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  have e5 : 1 / w5 ^ 2 = 4 * √2 := by
    rw [hw5, Real.sq_sqrt (by positivity)]; field_simp
  have e3 : 1 / w3 ^ 2 = 2 * √2 := by
    rw [hw3, Real.sq_sqrt (by positivity)]; field_simp
  have h53 : w5 ≤ w3 := by
    rw [hw5, hw3]; apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hsplit : ∫ v in w5..1, gL Ω v = (∫ v in w5..w3, gL Ω v) + ∫ v in w3..1, gL Ω v :=
    (intervalIntegral.integral_add_adjacent_intervals (gL_intInt Ω h0 h1 _ _ hw5p h53)
      (gL_intInt Ω h0 h1 _ _ hw3p hw31.le)).symm
  have hu := bl_upper Ω w5 w3 h0 h1 hw5p h53
  have hl := bl_lower Ω w3 h0 h1 hw3p hw31.le
  rw [e5, e3] at hu
  rw [e3] at hl
  set r := w3 ^ 3 / √(Ω + (1 - Ω) * w3 ^ 6)
  have hr : 0 ≤ r := by positivity
  rw [hsplit]
  norm_num at hl
  nlinarith

/-- The distance integral to the nearest source is at most `(1 − w₁)/(1 − w₃)` times the one to the middle
source (the integrand decreases). -/
theorem bl_ratio13 (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (1 - √(1 / (2 * √2))) * ∫ v in √(1 / √2)..1, gL Ω v ≤
      (1 - √(1 / √2)) * ∫ v in √(1 / (2 * √2))..1, gL Ω v := by
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
    (intervalIntegral.integral_add_adjacent_intervals (gL_intInt Ω h0 h1 _ _ hw3p h31)
      (gL_intInt Ω h0 h1 _ _ hw1p hw11.le)).symm
  have hanti := gL_anti Ω h0 h1 w3 1 hw3p
  -- above w₁ the integrand is at most its value at w₁, below at least
  have hA : ∫ v in w1..1, gL Ω v ≤ ∫ v in w1..1, gL Ω w1 := by
    apply intervalIntegral.integral_mono_on hw11.le (gL_intInt Ω h0 h1 _ _ hw1p hw11.le)
      intervalIntegrable_const
    intro v hv
    exact hanti ⟨h31, le_rfl.trans hw11.le⟩ ⟨h31.trans hv.1, hv.2⟩ hv.1
  have hB : ∫ v in w3..w1, gL Ω w1 ≤ ∫ v in w3..w1, gL Ω v := by
    apply intervalIntegral.integral_mono_on h31 intervalIntegrable_const
      (gL_intInt Ω h0 h1 _ _ hw3p h31)
    intro v hv
    exact hanti ⟨hv.1, hv.2.trans hw11.le⟩ ⟨h31, hw11.le⟩ hv.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
  rw [hsplit]
  have hg : 0 ≤ gL Ω w1 := gL_nonneg Ω w1
  nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ w1 - w3),
    mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ 1 - w1)]

/-- The distance integral to the nearest source is at most `(1 − w₁)/(1 − w₅)` times the one to the farthest
source (the integrand decreases). -/
theorem bl_ratio15 (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (1 - √(1 / (4 * √2))) * ∫ v in √(1 / √2)..1, gL Ω v ≤
      (1 - √(1 / √2)) * ∫ v in √(1 / (4 * √2))..1, gL Ω v := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  set w1 := √(1 / √2) with hw1
  set w5 := √(1 / (4 * √2)) with hw5
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have h51 : w5 ≤ w1 := by
    rw [hw1, hw5]; apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le hq; linarith
  have hsplit : ∫ v in w5..1, gL Ω v = (∫ v in w5..w1, gL Ω v) + ∫ v in w1..1, gL Ω v :=
    (intervalIntegral.integral_add_adjacent_intervals (gL_intInt Ω h0 h1 _ _ hw5p h51)
      (gL_intInt Ω h0 h1 _ _ hw1p hw11.le)).symm
  have hanti := gL_anti Ω h0 h1 w5 1 hw5p
  -- above w₁ the integrand is at most its value at w₁, below at least
  have hA : ∫ v in w1..1, gL Ω v ≤ ∫ v in w1..1, gL Ω w1 := by
    apply intervalIntegral.integral_mono_on hw11.le (gL_intInt Ω h0 h1 _ _ hw1p hw11.le)
      intervalIntegrable_const
    intro v hv
    exact hanti ⟨h51, le_rfl.trans hw11.le⟩ ⟨h51.trans hv.1, hv.2⟩ hv.1
  have hB : ∫ v in w5..w1, gL Ω w1 ≤ ∫ v in w5..w1, gL Ω v := by
    apply intervalIntegral.integral_mono_on h51 intervalIntegrable_const
      (gL_intInt Ω h0 h1 _ _ hw5p h51)
    intro v hv
    exact hanti ⟨hv.1, hv.2.trans hw11.le⟩ ⟨h51, hw11.le⟩ hv.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
  rw [hsplit]
  have hg : 0 ≤ gL Ω w1 := gL_nonneg Ω w1
  nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ w1 - w5),
    mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ 1 - w1)]

/-- The values of a cubic through the origin with slope one at one, three and five halves of `log 2`. -/
theorem bl_rel (a₂ a₃ : ℝ) :
    30 * (1 * Real.log 2 / 2 + a₂ / Real.log 10 * (1 * Real.log 2 / 2) ^ 2
        + a₃ / Real.log 10 ^ 2 * (1 * Real.log 2 / 2) ^ 3)
      - 20 / 3 * (3 * Real.log 2 / 2 + a₂ / Real.log 10 * (3 * Real.log 2 / 2) ^ 2
        + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2 / 2) ^ 3)
      + 6 / 5 * (5 * Real.log 2 / 2 + a₂ / Real.log 10 * (5 * Real.log 2 / 2) ^ 2
        + a₃ / Real.log 10 ^ 2 * (5 * Real.log 2 / 2) ^ 3) = 8 * Real.log 2 := by
  ring

/-- The bridge at one source of `fit_direction`: the distance is `s/H₀` times the integral from `√(1/s)`. -/
theorem bl_bridge (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (a : ℝ → ℝ) (t₅ t t₀ : ℝ) (h5 : t₅ ≤ t) (ht : t ≤ t₀)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hdiff : ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (S : ℝ) (hz : redshift a t₀ t = S - 1) :
    lumDistFlat a t₀ t = S / hubble a t₀ * ∫ v in √(1 / S)..1, gL Ω v := by
  have hsub : Icc t t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h5
  have hbr := lumDistFlat_flatLCDM Ω h0 h1 a t t₀ ht (fun s hs => hpos s (hsub hs))
    (fun s hs => hdiff s (hsub hs)) hH₀ (fun s hs => hH s (hsub hs))
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h5.trans ht, le_rfl⟩
  have ha : 0 < a t := hpos t ⟨h5, ht⟩
  have es : (1:ℝ) + (S - 1) = S := by ring
  rw [ratio_of_z a t t₀ _ ha ha₀ hz, es, hz, es] at hbr
  exact hbr

theorem bl_pos (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (w : ℝ) (hw : 0 < w) (hw1 : w < 1) (S H₀ : ℝ)
    (hS : 0 < S) (hH₀ : 0 < H₀) : 0 < S / H₀ * ∫ v in w..1, gL Ω v := by
  have := Jpos Ω w h0 h1 hw hw1; positivity

/-- Without `0 < P(√2 − 1)`: the value at the nearest source is positive anyway. -/
theorem fit_direction_r14 : dropped% Checked.Cosmography.B1Fit.fit_direction 14 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp3 hp5
    hm1 hm3 hm5
  rcases lt_or_ge 0 (logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) with hp1 | hp1
  · exact Checked.Cosmography.B1Fit.fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  exfalso
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb3 := bl_bridge Ω h0 h1 a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  have hb5 := bl_bridge Ω h0 h1 a t₅ t₅ t₀ le_rfl (h53.trans (h31.trans h10)) hpos hdiff hH₀ hH
    (4 * √2) hz5
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hb3]; exact bl_pos Ω h0 h1 _ hw3p hw31 _ _ (by positivity) hH₀
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by rw [hb5]; exact bl_pos Ω h0 h1 _ hw5p hw51 _ _ (by positivity) hH₀
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 := lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  rw [hz1, hL1] at hp1
  have hrel := bl_rel a₂ a₃
  set P1 := 1 * ℓ / 2 + a₂ / Real.log 10 * (1 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (1 * ℓ / 2) ^ 3
  set P3 := 3 * ℓ / 2 + a₂ / Real.log 10 * (3 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (3 * ℓ / 2) ^ 3
  set P5 := 5 * ℓ / 2 + a₂ / Real.log 10 * (5 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (5 * ℓ / 2) ^ 3
  have hP1 : P1 ≤ 0 := by
    by_contra hc; push Not at hc; have := div_pos hc hHp; linarith
  have hP3 : 0 < P3 := by
    have := hp3; rw [hz3, hL3] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have h := ratio_step _ _ _ _ c hd5 hd3 hp5 hp3 hm5 hm3
  rw [hb3, hb5, hz3, hz5, hL3, hL5] at h
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v
  have r := ratio_clean _ (2 * √2) (4 * √2) _ H J3 J5 P5 P3 2 (by positivity) hH₀ hHp (by ring) h
  have hJ3 : 0 < J3 := Jpos Ω _ h0 h1 hw3p hw31
  have hρ := bl_ratio53 Ω h0 h1
  -- κ J₃ P₅ ≤ 2 J₅ P₃ ≤ 2 ρ J₃ P₃ with ρ = (4√2 − 1)/(2√2 − 1) < 2.55, while P₅ > 50/9 P₃
  have hJ5 : (2 * √2 - 1) * J5 ≤ (4 * √2 - 1) * J3 := hρ
  have h2 : (2 * √2 - 1) * (95499 / 100000 * J3 * P5) ≤ 2 * (4 * √2 - 1) * J3 * P3 := by
    have hA0 : (0:ℝ) ≤ 2 * √2 - 1 := by linarith
    linarith only [mul_le_mul_of_nonneg_left r hA0,
      mul_le_mul_of_nonneg_right hJ5 (by linarith : (0:ℝ) ≤ 2 * P3)]
  have h3 : 6 / 5 * P5 > 20 / 3 * P3 := by linarith
  have h4 : (2 * √2 - 1) * (95499 / 100000) * P5 ≤ 2 * (4 * √2 - 1) * P3 := by
    have := h2; rw [show (2 * √2 - 1) * (95499 / 100000 * J3 * P5) = J3 * ((2 * √2 - 1) * (95499 / 100000) * P5)
      by ring, show 2 * (4 * √2 - 1) * J3 * P3 = J3 * (2 * (4 * √2 - 1) * P3) by ring] at this
    exact le_of_mul_le_mul_left this hJ3
  have hA : 0 < (2 * √2 - 1) * (95499 / 100000) := by
    have : (0:ℝ) < 2 * √2 - 1 := by linarith only [hq2l]
    positivity
  have h5 : (2 * √2 - 1) * (95499 / 100000) * (50 / 9 * P3) < (2 * √2 - 1) * (95499 / 100000) * P5 :=
    mul_lt_mul_of_pos_left (by linarith only [h3]) hA
  have h6 : 0 < ((2 * √2 - 1) * (95499 / 100000) * (50 / 9) - 2 * (4 * √2 - 1)) * P3 :=
    mul_pos (by linarith only [hq2l, hq2u]) hP3
  linarith only [h4, h5, h6]

/-- Without `0 < P(4√2 − 1)`: the value at the farthest source is positive anyway. -/
theorem fit_direction_r16 : dropped% Checked.Cosmography.B1Fit.fit_direction 16 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3
    hm1 hm3 hm5
  rcases lt_or_ge 0 (logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) with hp5 | hp5
  · exact Checked.Cosmography.B1Fit.fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  exfalso
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb1 := bl_bridge Ω h0 h1 a t₅ t₁ t₀ (h53.trans h31) h10 hpos hdiff hH₀ hH (√2) hz1
  have hb3 := bl_bridge Ω h0 h1 a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hb1]; exact bl_pos Ω h0 h1 _ hw1p hw11 _ _ hq hH₀
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hb3]; exact bl_pos Ω h0 h1 _ hw3p hw31 _ _ (by positivity) hH₀
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 := lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  rw [hz5, hL5] at hp5
  have hrel := bl_rel a₂ a₃
  set P1 := 1 * ℓ / 2 + a₂ / Real.log 10 * (1 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (1 * ℓ / 2) ^ 3
  set P3 := 3 * ℓ / 2 + a₂ / Real.log 10 * (3 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (3 * ℓ / 2) ^ 3
  set P5 := 5 * ℓ / 2 + a₂ / Real.log 10 * (5 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (5 * ℓ / 2) ^ 3
  have hP5 : P5 ≤ 0 := by
    by_contra hc; push Not at hc; have := div_pos hc hHp; linarith
  have hP3 : 0 < P3 := by
    have := hp3; rw [hz3, hL3] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have h := ratio_step _ _ _ _ c hd1 hd3 hp1 hp3 hm1 hm3
  rw [hb1, hb3, hz1, hz3, hL1, hL3] at h
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  have r := ratio_clean _ (2 * √2) (√2) _ H J3 J1 P1 P3 (1 / 2) (by positivity) hH₀ hHp (by ring) h
  have hJ3 : 0 < J3 := Jpos Ω _ h0 h1 hw3p hw31
  have hσ := bl_ratio13 Ω h0 h1
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  -- κ J₃ P₁ ≤ J₁ P₃ / 2 ≤ σ J₃ P₃ / 2 with σ = (1 − w₁)/(1 − w₃) < 0.393, while P₁ > 2/9 P₃
  have hJ1 : (1 - √(1 / (2 * √2))) * J1 ≤ (1 - 13139 / 15625) * J3 := by
    have : (1 - √(1 / √2)) * J3 ≤ (1 - 13139 / 15625) * J3 :=
      mul_le_mul_of_nonneg_right (by linarith) hJ3.le
    linarith
  have hA : 0 < 1 - √(1 / (2 * √2)) := by linarith
  have h2 : (1 - √(1 / (2 * √2))) * (95499 / 100000 * J3 * P1) ≤ 1 / 2 * (1 - 13139 / 15625) * J3 * P3 := by
    linarith only [mul_le_mul_of_nonneg_right hJ1 (by linarith : (0:ℝ) ≤ 1 / 2 * P3),
      mul_le_mul_of_nonneg_left r hA.le]
  have h4 : (1 - √(1 / (2 * √2))) * (95499 / 100000) * P1 ≤ 1 / 2 * (1 - 13139 / 15625) * P3 := by
    have := h2; rw [show (1 - √(1 / (2 * √2))) * (95499 / 100000 * J3 * P1)
        = J3 * ((1 - √(1 / (2 * √2))) * (95499 / 100000) * P1) by ring,
      show 1 / 2 * (1 - 13139 / 15625) * J3 * P3 = J3 * (1 / 2 * (1 - 13139 / 15625) * P3) by ring] at this
    exact le_of_mul_le_mul_left this hJ3
  have h3 : 30 * P1 > 20 / 3 * P3 := by linarith
  have hP1 : 0 < P1 := by linarith
  have h5 : (148651 / 250000 : ℝ) ≥ √(1 / (2 * √2)) := wb3l
  have h6 : (1 - 148651 / 250000) * (95499 / 100000) * P1 ≤ (1 - √(1 / (2 * √2))) * (95499 / 100000) * P1 := by
    apply mul_le_mul_of_nonneg_right _ hP1.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith
  linarith only [h4, h6, h3, hP3]

/-- `κ (15 J₁ + 12/5 J₅) ≥ 20/3 J₃` for every density between zero and one, with `κ = 0.95499` (the matching
tolerance): the nearest and farthest distances together are too large for a cubic with all three values negative. -/
theorem bl_comb (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    20 / 3 * ∫ v in √(1 / (2 * √2))..1, gL Ω v ≤
      95499 / 100000 * (15 * (∫ v in √(1 / √2)..1, gL Ω v) + 12 / 5 * ∫ v in √(1 / (4 * √2))..1, gL Ω v) := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  set w1 := √(1 / √2) with hw1
  set w3 := √(1 / (2 * √2)) with hw3
  set w5 := √(1 / (4 * √2)) with hw5
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have e1 : 1 / w1 ^ 2 = √2 := by rw [hw1, Real.sq_sqrt (by positivity)]; field_simp
  have e3 : 1 / w3 ^ 2 = 2 * √2 := by rw [hw3, Real.sq_sqrt (by positivity)]; field_simp
  have h31 : w3 ≤ w1 := by linarith
  have h53 : w5 ≤ w3 := by linarith
  have s1 : ∫ v in w3..1, gL Ω v = (∫ v in w3..w1, gL Ω v) + ∫ v in w1..1, gL Ω v :=
    (intervalIntegral.integral_add_adjacent_intervals (gL_intInt Ω h0 h1 _ _ hw3p h31)
      (gL_intInt Ω h0 h1 _ _ hw1p hw11.le)).symm
  have s5 : ∫ v in w5..1, gL Ω v = (∫ v in w5..w3, gL Ω v) + ∫ v in w3..1, gL Ω v :=
    (intervalIntegral.integral_add_adjacent_intervals (gL_intInt Ω h0 h1 _ _ hw5p h53)
      (gL_intInt Ω h0 h1 _ _ hw3p hw31.le)).symm
  rw [s5, s1]
  set J1 := ∫ v in w1..1, gL Ω v
  set M := ∫ v in w3..w1, gL Ω v
  set K := ∫ v in w5..w3, gL Ω v
  set φ := w1 ^ 3 / √(Ω + (1 - Ω) * w1 ^ 6) with hφ
  set G := gL Ω w3 with hG
  have hJ1 : φ * (√2 - 1) ≤ J1 := by
    have := bl_lower Ω w1 h0 h1 hw1p hw11.le; rw [e1] at this; norm_num at this; linarith
  have hM1 : M ≤ φ * (2 * √2 - √2) := by
    have := bl_upper Ω w3 w1 h0 h1 hw3p h31; rw [e1, e3] at this; exact this
  have hanti := gL_anti Ω h0 h1 w5 1 hw5p
  have hM2 : M ≤ G * (w1 - w3) := by
    have h := intervalIntegral.integral_mono_on h31 (gL_intInt Ω h0 h1 _ _ hw3p h31)
      (intervalIntegrable_const (c := G)) (fun v hv => hanti ⟨h53, hw31.le⟩
        ⟨h53.trans hv.1, hv.2.trans hw11.le⟩ hv.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h; linarith
  have hK : G * (w3 - w5) ≤ K := by
    have h := intervalIntegral.integral_mono_on h53 (intervalIntegrable_const (c := G))
      (gL_intInt Ω h0 h1 _ _ hw5p h53) (fun v hv => hanti ⟨hv.1, hv.2.trans hw31.le⟩
        ⟨h53, hw31.le⟩ hv.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h; linarith
  have hφ0 : 0 ≤ φ := by positivity
  have hG0 : 0 ≤ G := gL_nonneg Ω w3
  rcases le_total G (56 / 10 * φ) with hc | hc
  · -- M ≤ G (w₁ − w₃), K ≥ G (w₃ − w₅)
    have a1 : G * (w1 - w3) ≤ G * (2462940 / 10000000) :=
      mul_le_mul_of_nonneg_left (by linarith) hG0
    have a2 : G * (1741540 / 10000000) ≤ G * (w3 - w5) :=
      mul_le_mul_of_nonneg_left (by linarith) hG0
    have a3 : φ * (41421356 / 100000000) ≤ φ * (√2 - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hφ0
    linarith
  · -- M ≤ √2 φ
    have a2 : G * (1741540 / 10000000) ≤ G * (w3 - w5) :=
      mul_le_mul_of_nonneg_left (by linarith) hG0
    have a3 : φ * (41421356 / 100000000) ≤ φ * (√2 - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hφ0
    have a4 : φ * (2 * √2 - √2) ≤ φ * (141421357 / 100000000) :=
      mul_le_mul_of_nonneg_left (by linarith) hφ0
    linarith

/-- Without `0 < H`: a non-positive normalisation makes all three values of the cubic negative (zero is excluded by
the positive polynomial distances), and no such cubic matches the three distances. -/
theorem fit_direction_r13 : dropped% Checked.Cosmography.B1Fit.fit_direction 13 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hp1 hp3 hp5
    hm1 hm3 hm5
  rcases lt_or_ge 0 H with hHp | hHn
  · exact Checked.Cosmography.B1Fit.fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  exfalso
  rcases eq_or_lt_of_le hHn with hH0 | hHn
  · rw [hH0] at hp1; unfold logPolyDL3 at hp1; simp at hp1
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb1 := bl_bridge Ω h0 h1 a t₅ t₁ t₀ (h53.trans h31) h10 hpos hdiff hH₀ hH (√2) hz1
  have hb3 := bl_bridge Ω h0 h1 a t₅ t₃ t₀ h53 (h31.trans h10) hpos hdiff hH₀ hH (2 * √2) hz3
  have hb5 := bl_bridge Ω h0 h1 a t₅ t₅ t₀ le_rfl (h53.trans (h31.trans h10)) hpos hdiff hH₀ hH
    (4 * √2) hz5
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw3p, hw31⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hb1]; exact bl_pos Ω h0 h1 _ hw1p hw11 _ _ hq hH₀
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hb3]; exact bl_pos Ω h0 h1 _ hw3p hw31 _ _ (by positivity) hH₀
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by rw [hb5]; exact bl_pos Ω h0 h1 _ hw5p hw51 _ _ (by positivity) hH₀
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHn.ne hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHn.ne hu3
  have hL5 := lp_eq a₂ a₃ H _ _ hHn.ne hu5
  have hrel := bl_rel a₂ a₃
  set P1 := 1 * ℓ / 2 + a₂ / Real.log 10 * (1 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (1 * ℓ / 2) ^ 3
  set P3 := 3 * ℓ / 2 + a₂ / Real.log 10 * (3 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (3 * ℓ / 2) ^ 3
  set P5 := 5 * ℓ / 2 + a₂ / Real.log 10 * (5 * ℓ / 2) ^ 2 + a₃ / Real.log 10 ^ 2 * (5 * ℓ / 2) ^ 3
  have hN : ∀ P : ℝ, P / H = -P / -H := fun P => (neg_div_neg_eq P H).symm
  have hHm : 0 < -H := by linarith
  have hQ3 : 0 < -P3 := by
    have := hp3; rw [hz3, hL3, hN] at this; exact (div_pos_iff_of_pos_right hHm).1 this
  have ha := ratio_step _ _ _ _ c hd3 hd1 hp3 hp1 hm3 hm1
  rw [hb1, hb3, hz1, hz3, hL1, hL3, hN P1, hN P3] at ha
  have hc := ratio_step _ _ _ _ c hd3 hd5 hp3 hp5 hm3 hm5
  rw [hb5, hb3, hz5, hz3, hL5, hL3, hN P5, hN P3] at hc
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v
  have r13 := ratio_clean _ (√2) (2 * √2) _ (-H) J1 J3 (-P3) (-P1) 2 hq hH₀ hHm (by ring) ha
  have r53 := ratio_clean _ (4 * √2) (2 * √2) _ (-H) J5 J3 (-P3) (-P5) (1 / 2) (by positivity) hH₀ hHm
    (by ring) hc
  have hJ3 : 0 < J3 := Jpos Ω _ h0 h1 hw3p hw31
  have hcomb := bl_comb Ω h0 h1
  -- κ Q₃ (15 J₁ + 12/5 J₅) ≤ J₃ (30 Q₁ + 6/5 Q₅) < 20/3 J₃ Q₃ ≤ κ Q₃ (15 J₁ + 12/5 J₅)
  have h1' : J3 * (30 * -P1 + 6 / 5 * -P5) < J3 * (20 / 3 * -P3) :=
    mul_lt_mul_of_pos_left (by linarith only [hrel, hℓ0]) hJ3
  have h2' : 20 / 3 * J3 * -P3 ≤
      95499 / 100000 * (15 * J1 + 12 / 5 * J5) * -P3 := mul_le_mul_of_nonneg_right hcomb hQ3.le
  linarith only [h1', h2', r13, r53]

/-- Without `0 < P(2√2 − 1)`: if the value at the middle source is not positive, the cubic is convex enough that
the direction holds with a wide margin (the matching at the nearest and farthest sources alone). -/
theorem fit_direction_r15 : dropped% Checked.Cosmography.B1Fit.fit_direction 15 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp5
    hm1 hm3 hm5
  rcases lt_or_ge 0 (logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) with hp3 | hp3
  · exact Checked.Cosmography.B1Fit.fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq : 0 < √2 := by linarith
  have hb1 := bl_bridge Ω h0 h1 a t₅ t₁ t₀ (h53.trans h31) h10 hpos hdiff hH₀ hH (√2) hz1
  have hb5 := bl_bridge Ω h0 h1 a t₅ t₅ t₀ le_rfl (h53.trans (h31.trans h10)) hpos hdiff hH₀ hH
    (4 * √2) hz5
  obtain ⟨hw1p, hw11⟩ := w_lt_one (√2) (by linarith)
  obtain ⟨hw5p, hw51⟩ := w_lt_one (4 * √2) (by linarith)
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hb1]; exact bl_pos Ω h0 h1 _ hw1p hw11 _ _ hq hH₀
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by rw [hb5]; exact bl_pos Ω h0 h1 _ hw5p hw51 _ _ (by positivity) hH₀
  set ℓ := Real.log 2 with hℓ
  set l := Real.log 10 with hl
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 := lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 := lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 := lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  set B2 := a₂ / l * ℓ ^ 2 with hB2
  set B3 := a₃ / l ^ 2 * ℓ ^ 3 with hB3
  have eP1 : 1 * ℓ / 2 + a₂ / l * (1 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (1 * ℓ / 2) ^ 3
      = ℓ / 2 + B2 / 4 + B3 / 8 := by rw [hB2, hB3]; ring
  have eP3 : 3 * ℓ / 2 + a₂ / l * (3 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (3 * ℓ / 2) ^ 3
      = 3 * ℓ / 2 + 9 * B2 / 4 + 27 * B3 / 8 := by rw [hB2, hB3]; ring
  have eP5 : 5 * ℓ / 2 + a₂ / l * (5 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (5 * ℓ / 2) ^ 3
      = 5 * ℓ / 2 + 25 * B2 / 4 + 125 * B3 / 8 := by rw [hB2, hB3]; ring
  rw [eP1] at hL1
  rw [eP3] at hL3
  rw [eP5] at hL5
  have hP1 : 0 < ℓ / 2 + B2 / 4 + B3 / 8 := by
    have := hp1; rw [hz1, hL1] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have hP5 : 0 < 5 * ℓ / 2 + 25 * B2 / 4 + 125 * B3 / 8 := by
    have := hp5; rw [hz5, hL5] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have hP3 : 3 * ℓ / 2 + 9 * B2 / 4 + 27 * B3 / 8 ≤ 0 := by
    by_contra hc; push Not at hc; have := div_pos hc hHp; rw [hz3, hL3] at hp3; linarith
  have h := ratio_step _ _ _ _ c hd1 hd5 hp1 hp5 hm1 hm5
  rw [hb1, hb5, hz1, hz5, hL1, hL5] at h
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v
  set P1 := ℓ / 2 + B2 / 4 + B3 / 8
  set P5 := 5 * ℓ / 2 + 25 * B2 / 4 + 125 * B3 / 8
  have r := ratio_clean _ (4 * √2) (√2) _ H J5 J1 P1 P5 (1 / 4) (by positivity) hH₀ hHp (by ring) h
  have hJ5 : 0 < J5 := Jpos Ω _ h0 h1 hw5p hw51
  have hσ := bl_ratio15 Ω h0 h1
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  -- (1 − w₅) κ J₅ P₁ ≤ (1 − w₅) J₁ P₅ / 4 ≤ (1 − w₁) J₅ P₅ / 4
  have hA : 0 < 1 - √(1 / (4 * √2)) := by linarith
  have hJ1 : (1 - √(1 / (4 * √2))) * J1 ≤ (1 - 13139 / 15625) * J5 := by
    have : (1 - √(1 / √2)) * J5 ≤ (1 - 13139 / 15625) * J5 :=
      mul_le_mul_of_nonneg_right (by linarith) hJ5.le
    linarith
  have h2 : (1 - √(1 / (4 * √2))) * (95499 / 100000 * J5 * P1) ≤ 1 / 4 * (1 - 13139 / 15625) * J5 * P5 := by
    linarith only [mul_le_mul_of_nonneg_right hJ1 (by linarith : (0:ℝ) ≤ 1 / 4 * P5),
      mul_le_mul_of_nonneg_left r hA.le]
  have h4 : (1 - √(1 / (4 * √2))) * (95499 / 100000) * P1 ≤ 1 / 4 * (1 - 13139 / 15625) * P5 := by
    have := h2; rw [show (1 - √(1 / (4 * √2))) * (95499 / 100000 * J5 * P1)
        = J5 * ((1 - √(1 / (4 * √2))) * (95499 / 100000) * P1) by ring,
      show 1 / 4 * (1 - 13139 / 15625) * J5 * P5 = J5 * (1 / 4 * (1 - 13139 / 15625) * P5) by ring] at this
    exact le_of_mul_le_mul_left this hJ5
  have h6 : (1 - 420449 / 1000000) * (95499 / 100000) * P1 ≤ (1 - √(1 / (4 * √2))) * (95499 / 100000) * P1 := by
    apply mul_le_mul_of_nonneg_right _ hP1.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith
  -- the ΛCDM constant of the line is at most its value at density zero
  have hℓu : ℓ < 0.6931471808 := Real.log_two_lt_d9
  have hℓl : 0.6931471803 < ℓ := Real.log_two_gt_d9
  have hbr : 20 / 3 * (9 / 8 * Ω - 2) * ℓ + 3 / 4 ≤ 0 := by
    have : (9 / 8 * Ω - 2) * ℓ ≤ -(7 / 8) * ℓ := mul_le_mul_of_nonneg_right (by linarith) hℓ0.le
    have e : 20 / 3 * (9 / 8 * Ω - 2) * ℓ = 20 / 3 * ((9 / 8 * Ω - 2) * ℓ) := by ring
    rw [e]
    have hl' : (0.6931471803 : ℝ) < ℓ := hℓl
    linarith only [this, hl']
  have hC0 : 20 / 3 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6) * ℓ ^ 3 - (3 / 2 - 3 / 4 * Ω) * ℓ ^ 2
      - (20 / 3 * (7 / 6) * ℓ ^ 3 - 3 / 2 * ℓ ^ 2) = Ω * ℓ ^ 2 * (20 / 3 * (9 / 8 * Ω - 2) * ℓ + 3 / 4) := by
    ring
  have hC1 : Ω * ℓ ^ 2 * (20 / 3 * (9 / 8 * Ω - 2) * ℓ + 3 / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hbr
  have hl3 : ℓ ^ 3 ≤ 0.6931471808 ^ 3 := pow_le_pow_left₀ hℓ0.le hℓu.le 3
  have hl2 : 0.6931471803 ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by norm_num) hℓl.le 2
  have hC : 20 / 3 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6) * ℓ ^ 3 - (3 / 2 - 3 / 4 * Ω) * ℓ ^ 2
      ≤ 18696 / 10000 := by norm_num at hl3 hl2 ⊢; linarith
  apply conclude Ω a₂ a₃ ((a₂ / l - (3 / 2 - 3 / 4 * Ω)) * ℓ ^ 2)
    ((a₃ / l ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * ℓ ^ 3) rfl rfl
  have eG : 20 / 3 * ((a₃ / l ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * ℓ ^ 3)
      - (a₂ / l - (3 / 2 - 3 / 4 * Ω)) * ℓ ^ 2 = 20 / 3 * B3 - B2
        - (20 / 3 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6) * ℓ ^ 3 - (3 / 2 - 3 / 4 * Ω) * ℓ ^ 2) := by
    rw [hB2, hB3]; ring
  rw [eG]
  have dP1 : P1 = ℓ / 2 + B2 / 4 + B3 / 8 := rfl
  have dP5 : P5 = 5 * ℓ / 2 + 25 * B2 / 4 + 125 * B3 / 8 := rfl
  linarith only [hC, hP1, hP3, h4, h6, hℓl, hℓu, dP1, dP5]

end Checked.Trust.NCBL
