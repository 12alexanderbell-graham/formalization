import Mathlib

/-! Scratch (run 2026-11-13T0228Z, part 1): an explicit profile meeting every hypothesis of the monotone-class
stagnation-point window headlines except `p' = q`, with wall value q(0) ≥ 2. -/

namespace Scratch.ProfileT
open Set Filter Topology intervalIntegral

noncomputable def fT (η : ℝ) : ℝ := η + 1 - (2 * η + 1) * Real.exp (-η)
noncomputable def pT (η : ℝ) : ℝ := 1 - (1 - 2 * η) * Real.exp (-η)

theorem fT_deriv (η : ℝ) : HasDerivAt fT (pT η) η := by
  have he : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-η)) η := by
    simpa using (hasDerivAt_neg η).exp
  have h := (((hasDerivAt_id η).add_const 1).sub
    ((((hasDerivAt_id η).const_mul 2).add_const 1).mul he))
  unfold fT pT
  convert h using 1
  · ext x; simp
  · simp; ring

theorem fT_cont : Continuous fT := by unfold fT; fun_prop
theorem pT_cont : Continuous pT := by unfold pT; fun_prop

theorem fT_zero : fT 0 = 0 := by simp [fT]
theorem pT_zero : pT 0 = 0 := by simp [pT]

theorem pT_lim : Tendsto pT atTop (𝓝 1) := by
  have h1 : Tendsto (fun η : ℝ => Real.exp (-η)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun η : ℝ => η * Real.exp (-η)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h3 : Tendsto (fun η : ℝ => 1 - (Real.exp (-η) - 2 * (η * Real.exp (-η)))) atTop (𝓝 (1 - (0 - 2 * 0))) :=
    tendsto_const_nhds.sub (h1.sub (h2.const_mul 2))
  simp only [mul_zero, sub_zero] at h3
  refine h3.congr (fun η => ?_)
  unfold pT; ring

theorem pT_ge_one {η : ℝ} (h : 1 / 2 ≤ η) : 1 ≤ pT η := by
  unfold pT
  have : (1 - 2 * η) * Real.exp (-η) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
  linarith

/-- G = ∫₀^η f. -/
noncomputable def GT (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, fT s

theorem GT_deriv (η : ℝ) : HasDerivAt GT (fT η) η :=
  (fT_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem GT_cont : Continuous GT := continuous_iff_continuousAt.2 fun η => (GT_deriv η).continuousAt

/-- The integrand e^{kG}(p² − 1). -/
noncomputable def rT (k s : ℝ) : ℝ := Real.exp (k * GT s) * (pT s ^ 2 - 1)

theorem rT_cont (k : ℝ) : Continuous (rT k) := by
  unfold rT; have := GT_cont; have := pT_cont; fun_prop

/-- The wall value: 2 plus ∫₀^{1/2} e^{kG}. -/
noncomputable def q0T (k : ℝ) : ℝ := 2 + ∫ s in (0 : ℝ)..(1 / 2), Real.exp (k * GT s)

noncomputable def qT (k η : ℝ) : ℝ := Real.exp (-(k * GT η)) * (q0T k + ∫ s in (0 : ℝ)..η, rT k s)

theorem qT_deriv (k η : ℝ) : HasDerivAt (qT k) (-(k * fT η * qT k η) - 1 + pT η ^ 2) η := by
  have hI : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, rT k s) (rT k η) η :=
    ((rT_cont k).integral_hasStrictDerivAt 0 η).hasDerivAt
  have hE : HasDerivAt (fun u => Real.exp (-(k * GT u))) (Real.exp (-(k * GT η)) * (-(k * fT η))) η :=
    ((GT_deriv η).const_mul k).neg.exp
  have h := hE.mul (hI.const_add (q0T k))
  unfold qT
  convert h using 1
  unfold rT
  have : Real.exp (-(k * GT η)) * Real.exp (k * GT η) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (1 - pT η ^ 2) * this

theorem expG_int (k : ℝ) (a b : ℝ) : IntervalIntegrable (fun s => Real.exp (k * GT s)) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable; have := GT_cont; fun_prop

/-- The bracket stays at least 2. -/
theorem bracket_ge (k η : ℝ) (hη : 0 ≤ η) : 2 ≤ q0T k + ∫ s in (0 : ℝ)..η, rT k s := by
  have hlow : ∀ s, -Real.exp (k * GT s) ≤ rT k s := fun s => by
    unfold rT
    have := Real.exp_pos (k * GT s)
    nlinarith [sq_nonneg (pT s)]
  have hpos : ∀ s, 0 ≤ Real.exp (k * GT s) := fun s => (Real.exp_pos _).le
  unfold q0T
  rcases le_or_gt η (1 / 2) with h | h
  · -- ∫₀^η r ≥ −∫₀^η e^{kG} ≥ −∫₀^{1/2} e^{kG}
    have i1 : ∫ s in (0 : ℝ)..η, -Real.exp (k * GT s) ≤ ∫ s in (0 : ℝ)..η, rT k s :=
      intervalIntegral.integral_mono_on hη ((expG_int k 0 η).neg) ((rT_cont k).intervalIntegrable 0 η)
        (fun s _ => hlow s)
    have i2 : ∫ s in (0 : ℝ)..η, Real.exp (k * GT s) ≤ ∫ s in (0 : ℝ)..(1 / 2), Real.exp (k * GT s) := by
      have := intervalIntegral.integral_interval_sub_left (expG_int k 0 (1 / 2)) (expG_int k 0 η)
      have h3 : 0 ≤ ∫ s in η..(1 / 2), Real.exp (k * GT s) :=
        intervalIntegral.integral_nonneg h (fun s _ => hpos s)
      linarith
    rw [intervalIntegral.integral_neg] at i1
    linarith
  · have split := intervalIntegral.integral_add_adjacent_intervals
      ((rT_cont k).intervalIntegrable (μ := MeasureTheory.volume) 0 (1 / 2))
      ((rT_cont k).intervalIntegrable (μ := MeasureTheory.volume) (1 / 2) η)
    have i1 : ∫ s in (0 : ℝ)..(1 / 2), -Real.exp (k * GT s) ≤ ∫ s in (0 : ℝ)..(1 / 2), rT k s :=
      intervalIntegral.integral_mono_on (by norm_num) ((expG_int k 0 (1 / 2)).neg)
        ((rT_cont k).intervalIntegrable 0 (1 / 2)) (fun s _ => hlow s)
    have i2 : 0 ≤ ∫ s in (1 / 2 : ℝ)..η, rT k s := by
      apply intervalIntegral.integral_nonneg h.le
      intro s hs
      unfold rT
      have h1 := pT_ge_one hs.1
      exact mul_nonneg (hpos s) (by nlinarith)
    rw [intervalIntegral.integral_neg] at i1
    linarith

theorem qT_pos (k η : ℝ) (hη : 0 ≤ η) : 0 < qT k η := by
  unfold qT
  exact mul_pos (Real.exp_pos _) (by linarith [bracket_ge k η hη])

theorem qT_zero_ge (k : ℝ) : 2 ≤ qT k 0 := by
  have := bracket_ge k 0 le_rfl
  unfold qT; simp [GT] at this ⊢; linarith

end Scratch.ProfileT
