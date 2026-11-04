import Work.Cosmography.B1FitCerts

/-!
# B1 at fit level: across the quasar redshift range, every cubic log-polynomial that matches exact flat ΛCDM is displaced from the ΛCDM-implied point toward larger a₃ (any Ω_M ∈ [0, 1])

**Question (STATE "B1", next step 2; FINDINGS candidate C27; referee 0828Z §3.4).**
Risaliti & Lusso 2019 (Nat. Astron. 3, 272; arXiv:1811.02590) and Lusso et al. 2019
(A&A 628, L4; arXiv:1907.07692) fit `D_L = ln(10)(c/H₀)(x + a₂x² + a₃x³)`, `x = log₁₀(1+z)`,
and measure their > 4σ tension as the distance of the fitted `(a₂, a₃)` from the point flat ΛCDM
implies (`lusA2 Ω`, `lusA3 Ω`, Lusso et al. 2019 Eq. (8)). Yang et al. 2020 (arXiv:1911.01681)
and Banerjee et al. 2021 (arXiv:2009.04109) argue that the cubic is a poor approximant, so that
"ΛCDM seen through the cubic" is not the Taylor point. The earlier certified results
(`Checked.Cosmography.B1Sep.cubic_separation`, `cubic_direction`) used a two-point criterion at
z = 3 and z = 7 (outside the quasar range) and Ω ∈ [0.2, 0.4]; the referee asked for a statement
about fits over the data range and the whole ΛCDM line Ω ∈ [0, 1].

**Statement.** For every flat ΛCDM model with `Ω ∈ [0, 1]` (Friedmann law on the whole interval
back to the farthest source), take sources at the three redshifts with `1 + z = √2, 2√2, 4√2`
(`z ≈ 0.414, 1.828, 4.657`, spanning the RL19 quasar range `z ≤ 5.1`). Every cubic
log-polynomial — any `a₂, a₃`, normalisation `H > 0`, magnitude offset `c`, positive at the three
redshifts — whose distance modulus agrees with the exact one up to the common offset `c` within
0.05 mag at all three redshifts satisfies
`a₂ − a₂^ΛCDM + 1/2 < (20/3) log₁₀2 · (a₃ − a₃^ΛCDM)`
(slope `(20/3) log₁₀ 2 ≈ 2.007`): it lies strictly beyond a line through the ΛCDM-implied point,
on the side of smaller `a₂` / larger `a₃`, by a definite margin.

Why "fit level": a least-squares fit of the cubic to exact ΛCDM over `z ≤ 5.1` (uniform in z or
in ln(1+z)) leaves residuals within ±0.031 mag of a common offset at these three redshifts for every
Ω ≥ 0.1 (referee `runs/2026-11-04T0228Z/referee_b1fit.md`; floating point; at Ω = 0.04 the
half-range is 0.054 and at Ω = 0 it is 0.19, so near Ω = 0 such fits are not covered), so such fits
satisfy the hypothesis; the Taylor point itself does not (its residual half-range at the three
points is 0.11–0.23 mag for Ω ≥ 0.1, up to 0.81 at Ω = 0). The hypothesis is weaker than agreement
on the whole range, so the theorem also covers every minimax fit within 0.05 mag over any range
containing the three redshifts. It is not a statement about fits to data with errors; fits
dominated by low-redshift supernovae sit near the edge of the 0.05 mag condition at Ω = 0.3
(half-range 0.047–0.057, referee §3), and at 0.1 mag the conclusion fails (referee: minimum −3.97).

What it says about RL19 (C27): the RL19 Fig. 3 contour centre, read once at `(3.45, 1.6)`, lies on
the *other* side of the line for every Ω ∈ [0, 1] (`(20/3)log₁₀2·Δa₃ − Δa₂ ≤ −1.21`, referee and
author numerics). This is a side-of-line statement: truncation does not move ΛCDM's cubic image
toward the RL19 centre. It is not a statement that every matching cubic is farther from the RL19
centre than the ΛCDM point is (the theorem alone gives only distance ≥ 0.76). Mechanism and the
displacement by mocks: Yang et al. 2020, Banerjee et al. 2021; new here is the certified,
Ω-uniform direction over the data range and its comparison with the RL19 offset.

Positivity of the polynomial distance at the three redshifts is assumed (a negative distance has
no distance modulus; `Real.logb` would silently take the absolute value).

Conventions: as `Checked.Cosmography.B1` (`c = 1`, `hubble a t = ȧ/a`,
`redshift a t₀ t = a(t₀)/a(t) − 1`, `lumDistFlat`; distance-modulus difference `5 log₁₀(d/d')`).

FROZEN (annex 40.1) in run 2026-11-04T0228Z before proof work.
-/

namespace Work.Cosmography.B1Fit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-! ## Proof tools (not part of the frozen statement) -/

lemma lp_eq (a₂ a₃ H z u : ℝ) (hH : H ≠ 0) (hu : Real.log (1 + z) = u) :
    logPolyDL3 a₂ a₃ H z = (u + a₂ / Real.log 10 * u ^ 2 + a₃ / Real.log 10 ^ 2 * u ^ 3) / H := by
  have hl : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold logPolyDL3 Real.logb
  rw [hu]; field_simp

lemma wb (s wl wu : ℝ) (hs : 0 < s) (hwl : 0 ≤ wl) (h1 : wu ^ 2 * s ≤ 1)
    (h2 : 1 ≤ wl ^ 2 * s) : wu ≤ √(1 / s) ∧ √(1 / s) ≤ wl := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by rw [le_div_iff₀ hs]; exact h1)
  · rw [show wl = √(wl ^ 2) from (Real.sqrt_sq hwl).symm]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hs]; exact h2

lemma w_lt_one (s : ℝ) (hs : 1 < s) : 0 < √(1 / s) ∧ √(1 / s) < 1 := by
  have hs0 : 0 < s := by linarith
  refine ⟨Real.sqrt_pos.2 (by positivity), ?_⟩
  have h : √(1 / s) < √1 := Real.sqrt_lt_sqrt (by positivity) (by rw [div_lt_one hs0]; exact hs)
  rwa [Real.sqrt_one] at h

lemma Jpos (Ω w : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (hw : 0 < w) (hw1 : w < 1) :
    0 < ∫ v in w..1, gL Ω v := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (gL_intInt Ω h0 h1 w 1 hw hw1.le) _ hw1
  intro v hv
  unfold gL
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (inner_pos Ω v h0 h1 (lt_trans hw hv.1)))

lemma sqrt2_bounds : (141421356 / 100000000 : ℝ) ≤ √2 ∧ √2 ≤ 141421357 / 100000000 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · rw [show (141421357 / 100000000 : ℝ) = √((141421357 / 100000000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)


/-- General form (sources anywhere in `[t₅, t₀]`, no order between `t₁` and `t₃` assumed); the
frozen theorem below is its instance. -/
theorem fit_direction_gen (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (ht₁ : t₁ ∈ Set.Icc t₅ t₀) (ht₃ : t₃ ∈ Set.Icc t₅ t₀)
    (h₅₀ : t₅ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅))
    (hm₁ : |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
      ≤ 1 / 20)
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₅ : |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
      ≤ 1 / 20) :
    a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  -- sources and the bridge to the integral
  have h₁₀ : t₁ ≤ t₀ := ht₁.2
  have h₃₀ : t₃ ≤ t₀ := ht₃.2
  have hsub1 : Set.Icc t₁ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left ht₁.1
  have hsub3 : Set.Icc t₃ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left ht₃.1
  have hbr1 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₁ t₀ h₁₀ (fun s hs => hpos s (hsub1 hs))
    (fun s hs => hdiff s (hsub1 hs)) hH₀ (fun s hs => hH s (hsub1 hs))
  have hbr3 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub3 hs))
    (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH s (hsub3 hs))
  have hbr5 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₅ t₀ h₅₀ hpos hdiff hH₀ hH
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha1 : 0 < a t₁ := hpos t₁ ht₁
  have ha3 : 0 < a t₃ := hpos t₃ ht₃
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₁ t₀ _ ha1 ha₀ hz₁, es1, hz₁, es1] at hbr1
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hbr3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hbr5
  change lumDistFlat a t₀ t₁ = √2 / hubble a t₀ * ∫ v in √(1 / √2)..1, gL Ω v at hbr1
  change lumDistFlat a t₀ t₃ = 2 * √2 / hubble a t₀ * ∫ v in √(1 / (2 * √2))..1, gL Ω v at hbr3
  change lumDistFlat a t₀ t₅ = 4 * √2 / hubble a t₀ * ∫ v in √(1 / (4 * √2))..1, gL Ω v at hbr5
  set J1 := ∫ v in √(1 / √2)..1, gL Ω v with hJ1
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v with hJ5
  set H₀ := hubble a t₀ with hH₀def
  -- the log-polynomial in u = ln(1+z)
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  set P1 := 1 * ℓ / 2 + a₂ / l * (1 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (1 * ℓ / 2) ^ 3 with hP1def
  set P3 := 3 * ℓ / 2 + a₂ / l * (3 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (3 * ℓ / 2) ^ 3 with hP3def
  set P5 := 5 * ℓ / 2 + a₂ / l * (5 * ℓ / 2) ^ 2 + a₃ / l ^ 2 * (5 * ℓ / 2) ^ 3 with hP5def
  have hL1 : logPolyDL3 a₂ a₃ H (redshift a t₀ t₁) = P1 / H := by
    rw [hz₁]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu1
  have hL3 : logPolyDL3 a₂ a₃ H (redshift a t₀ t₃) = P3 / H := by
    rw [hz₃]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu3
  have hL5 : logPolyDL3 a₂ a₃ H (redshift a t₀ t₅) = P5 / H := by
    rw [hz₅]; exact lp_eq a₂ a₃ H _ _ hHp.ne' hu5
  have hp1' : 0 < P1 := by
    have := hp₁; rw [hL1] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have hp3' : 0 < P3 := by
    have := hp₃; rw [hL3] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  have hp5' : 0 < P5 := by
    have := hp₅; rw [hL5] at this; exact (div_pos_iff_of_pos_right hHp).1 this
  -- integral limits
  have hs1 : 1 < √2 := by linarith
  have hs3 : 1 < 2 * √2 := by linarith
  have hs5 : 1 < 4 * √2 := by linarith
  obtain ⟨hw1p, hw1⟩ := w_lt_one _ hs1
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  have hJ1p : 0 < J1 := Jpos Ω _ hΩ₀ hΩ₁ hw1p hw1
  have hJ3p : 0 < J3 := Jpos Ω _ hΩ₀ hΩ₁ hw3p hw3
  have hJ5p : 0 < J5 := Jpos Ω _ hΩ₀ hΩ₁ hw5p hw5
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq2
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have hJ1l : ∫ v in (840897 / 1000000 : ℝ)..1, gL Ω v ≤ J1 :=
    J_shift Ω hΩ₀ hΩ₁ _ _ hw1p wb1l (by norm_num)
  have hJ1u : J1 ≤ ∫ v in (13139 / 15625 : ℝ)..1, gL Ω v :=
    J_shift Ω hΩ₀ hΩ₁ _ _ (by norm_num) wb1u hw1.le
  have hJ3u : J3 ≤ ∫ v in (594603 / 1000000 : ℝ)..1, gL Ω v :=
    J_shift Ω hΩ₀ hΩ₁ _ _ (by norm_num) wb3u hw3.le
  have hJ5l : ∫ v in (420449 / 1000000 : ℝ)..1, gL Ω v ≤ J5 :=
    J_shift Ω hΩ₀ hΩ₁ _ _ hw5p wb5l (by norm_num)
  -- the three matching conditions as distance ratios
  have hd1 : 0 < lumDistFlat a t₀ t₁ := by rw [hbr1]; positivity
  have hd3 : 0 < lumDistFlat a t₀ t₃ := by rw [hbr3]; positivity
  have hd5 : 0 < lumDistFlat a t₀ t₅ := by rw [hbr5]; positivity
  have r31 : 95499 / 100000 * J1 * P3 ≤ 2 * J3 * P1 := by
    have h := ratio_step _ _ _ _ c hd3 hd1 hp₃ hp₁ hm₃ hm₁
    rw [hbr1, hbr3, hL1, hL3] at h
    exact ratio_clean _ (√2) (2 * √2) H₀ H J1 J3 P3 P1 2 hq2 hH₀ hHp (by ring) h
  have r35 : 95499 / 100000 * J5 * P3 ≤ 1 / 2 * J3 * P5 := by
    have h := ratio_step _ _ _ _ c hd3 hd5 hp₃ hp₅ hm₃ hm₅
    rw [hbr5, hbr3, hL5, hL3] at h
    exact ratio_clean _ (4 * √2) (2 * √2) H₀ H J5 J3 P3 P5 (1 / 2) (by positivity) hH₀ hHp
      (by ring) h
  have r15 : 95499 / 100000 * J5 * P1 ≤ 1 / 4 * J1 * P5 := by
    have h := ratio_step _ _ _ _ c hd1 hd5 hp₁ hp₅ hm₁ hm₅
    rw [hbr5, hbr1, hL5, hL1] at h
    exact ratio_clean _ (4 * √2) (√2) H₀ H J5 J1 P1 P5 (1 / 4) (by positivity) hH₀ hHp
      (by ring) h
  -- displacement from the ΛCDM-implied point, rescaled
  set e₂ := (a₂ / l - (3 / 2 - 3 / 4 * Ω)) * ℓ ^ 2 with he₂
  set e₃ := (a₃ / l ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * ℓ ^ 3 with he₃
  have hP1 : P1 = Qf Ω (1 * ℓ / 2) + 1 / 4 * e₂ + 1 / 8 * e₃ := by
    rw [hP1def, he₂, he₃]; unfold Qf; ring
  have hP3 : P3 = Qf Ω (3 * ℓ / 2) + 9 / 4 * e₂ + 27 / 8 * e₃ := by
    rw [hP3def, he₂, he₃]; unfold Qf; ring
  have hP5 : P5 = Qf Ω (5 * ℓ / 2) + 25 / 4 * e₂ + 125 / 8 * e₃ := by
    rw [hP5def, he₂, he₃]; unfold Qf; ring
  have hcore := core Ω e₂ e₃ P1 P3 P5 J1 J3 J5 hΩ₀ hΩ₁ hP1 hP3 hP5 hp1' hp3' hp5' r31 r35 r15
    hJ1l hJ1u hJ3u hJ5l
  exact conclude Ω a₂ a₃ e₂ e₃ he₂ he₃ hcore

/-- **B1 at fit level (direction).** In every flat ΛCDM model with `Ω ∈ [0, 1]`, with sources at
`1 + z = √2, 2√2, 4√2` (`z ≈ 0.41, 1.83, 4.66`), every cubic log-polynomial (coefficients
`a₂, a₃`, normalisation `H > 0`, positive at the three redshifts) whose distance modulus agrees
with the exact one up to a common offset `c` within 0.05 mag at all three redshifts satisfies
`a₂ − lusA2 Ω + 1/2 < (20/3) log₁₀ 2 · (a₃ − lusA3 Ω)`: it lies beyond a line through the
ΛCDM-implied point, towards smaller `a₂` and larger `a₃`, by a margin of 1/2 in `a₂`. -/
theorem fit_direction (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₁ : t₃ ≤ t₁) (h₁₀ : t₁ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅))
    (hm₁ : |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
      ≤ 1 / 20)
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₅ : |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
      ≤ 1 / 20) :
    a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  exact fit_direction_gen Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ ⟨le_trans h₅₃ h₃₁, h₁₀⟩
    ⟨h₅₃, le_trans h₃₁ h₁₀⟩ (le_trans h₅₃ (le_trans h₃₁ h₁₀)) hpos hdiff hH₀ hH hz₁ hz₃ hz₅
    a₂ a₃ H c hHp hp₁ hp₃ hp₅ hm₁ hm₃ hm₅

end Work.Cosmography.B1Fit
