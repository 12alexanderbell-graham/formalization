/-- `yⁿ` is not `o(yⁿ)` from the past. -/
lemma not_isLittleO_self_past (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    (h : (fun t => c * yred a t₀ t ^ n) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ n)) : False := by
  have hself : (fun t => yred a t₀ t ^ n) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ n) :=
    (h.const_mul_left c⁻¹).congr' (Eventually.of_forall fun t => by
      simp only; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]) EventuallyEq.rfl
  have hev := (hasDerivAt_yred a t₀ hd ha0).eventually_ne (c := 0) (neg_ne_zero.2 hH)
  have hev' : ∀ᶠ t in 𝓝[<] t₀, yred a t₀ t ≠ 0 :=
    nhdsWithin_mono t₀ (fun t (ht : t < t₀) => ne_of_lt ht) hev
  have hfreq : ∃ᶠ t in 𝓝[<] t₀, ‖yred a t₀ t ^ n‖ ≠ 0 :=
    (hev'.mono fun t ht => by simpa using ht).frequently
  exact isLittleO_irrefl' hfreq hself

lemma yred_tendsto_past (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0) :
    Tendsto (fun t => yred a t₀ t) (𝓝[<] t₀) (𝓝 0) := by
  have h := (hasDerivAt_yred a t₀ hd ha0).continuousAt.tendsto
  have hy0 : yred a t₀ t₀ = 0 := by
    simp only [yred, redshift, div_self ha0, sub_self, zero_div]
  rw [hy0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The printed `D³_{L,y}` (with the corrected `D²`) fails, from the past, in every `C⁵` model
with `a(t₀) ≠ 0`, `H₀ ≠ 0`, `Ω₀ ≠ 1` and `q₀ ≠ 2/3`. -/
theorem printedD3y_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) ≠ 0) :
    ¬ (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hy0 := yred_tendsto_past a t₀ hd ha0
  have h54 : (fun t => yred a t₀ t ^ 5) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4) := by
    simpa using pow_succ_mul_isLittleO hy0 4 (fun _ => (1 : ℝ)) (isBigO_refl _ _)
  have hc := ((lumDist_y_fifth_order K a t₀ ha ha0 hH).mono
    (nhdsWithin_le_nhds (s := Set.Iio t₀))).trans h54
  have hd4 := h54.const_mul_left (correctD4y (decel a t₀) (cosmoCoeff 3 a t₀)
    (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (omega0 K a t₀))
  set c : ℝ := (omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) / 6 with hcdef
  have hc0 : c ≠ 0 := div_ne_zero hD (by norm_num)
  have hdiff : (fun t => c * yred a t₀ t ^ 4) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4) := by
    refine ((hp.sub hc).sub hd4).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [remK, seriesY4, correctD3y, hcdef]; ring
  exact not_isLittleO_self_past a t₀ hd ha0 hH 4 hc0 hdiff

/-- Two-sided version. -/
theorem printedD3y_fails (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) ≠ 0) :
    ¬ (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 4) :=
  fun hp => printedD3y_fails_past K a t₀ ha ha0 hH hD
    (hp.mono (nhdsWithin_le_nhds (s := Set.Iio t₀)))

/-- The printed `D⁴_{L,y}` (with corrected `D²`, `D³`) fails, from the past, in every `C⁵` model
with `a(t₀) ≠ 0`, `H₀ ≠ 0` and `(Ω₀ − 1)²/120 + 5 q₀ (Ω₀ − 1)/12 ≠ 0`. -/
theorem printedD4y_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) ^ 2 / 120 + 5 * decel a t₀ * (omega0 K a t₀ - 1) / 12 ≠ 0) :
    ¬ (fun t => remK correctD2y correctD3y printedD4y K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (lumDist_y_fifth_order K a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  set c : ℝ := (omega0 K a t₀ - 1) ^ 2 / 120 + 5 * decel a t₀ * (omega0 K a t₀ - 1) / 12
    with hcdef
  have hdiff : (fun t => c * yred a t₀ t ^ 5) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5) := by
    refine (hp.sub hc).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [remK, seriesY4, correctD4y, hcdef]; ring
  exact not_isLittleO_self_past a t₀ hd ha0 hH 5 hD hdiff

/-- Two-sided version. -/
theorem printedD4y_fails (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) ^ 2 / 120 + 5 * decel a t₀ * (omega0 K a t₀ - 1) / 12 ≠ 0) :
    ¬ (fun t => remK correctD2y correctD3y printedD4y K a t₀ t)
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5) :=
  fun hp => printedD4y_fails_past K a t₀ ha ha0 hH hD
    (hp.mono (nhdsWithin_le_nhds (s := Set.Iio t₀)))

/-- de Sitter expansion `a = exp` at `t₀ = 0` with closed spatial sections `K = 1`:
`H₀ = 1`, `q₀ = −1`, `Ω₀ = 2`. -/
lemma closedExp_vals : hubble Real.exp 0 = 1 ∧ decel Real.exp 0 = -1 ∧ omega0 1 Real.exp 0 = 2 := by
  have hH : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]
  refine ⟨hH, by simp [decel, Real.deriv_exp], ?_⟩
  simp only [omega0, hH]; norm_num

theorem bambaD3yClaim_false : ¬ BambaD3yClaim := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD3y_fails 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

theorem bambaD4yClaim_false : ¬ BambaD4yClaim := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD4y_fails 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

theorem bambaD3yClaimPast_false : ¬ BambaD3yClaimPast := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD3y_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

theorem bambaD4yClaimPast_false : ¬ BambaD4yClaimPast := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD4y_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

/-- Milne universe (`a(t) = t`, `K = −1`, observed at `t₀ = 1`; empty open FLRW, exact
`H₀ d_L = z + z²/2`): `H₀ = 1`, `q₀ = 0`, `Ω₀ = 0`. -/
lemma milne_vals : hubble (fun t => t) 1 = 1 ∧ decel (fun t => t) 1 = 0 ∧
    omega0 (-1) (fun t => t) 1 = 0 := by
  have hH : hubble (fun t => t) 1 = 1 := by simp [hubble]
  refine ⟨hH, by simp [decel], ?_⟩
  simp only [omega0, hH]; norm_num

/-- Both printed curvature terms fail in the Milne universe, from the past. -/
theorem milne_printedD3y_fails_past :
    ¬ (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) (-1) (fun t => t) 1 t)
      =o[𝓝[<] 1] (fun t => yred (fun t => t) 1 t ^ 4) := by
  obtain ⟨hH, hq, hΩ⟩ := milne_vals
  exact printedD3y_fails_past (-1) (fun t => t) 1 contDiffAt_id one_ne_zero
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)

theorem milne_printedD4y_fails_past :
    ¬ (fun t => remK correctD2y correctD3y printedD4y (-1) (fun t => t) 1 t)
      =o[𝓝[<] 1] (fun t => yred (fun t => t) 1 t ^ 5) := by
  obtain ⟨hH, hq, hΩ⟩ := milne_vals
  exact printedD4y_fails_past (-1) (fun t => t) 1 contDiffAt_id one_ne_zero
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
