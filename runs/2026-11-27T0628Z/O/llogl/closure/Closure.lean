import Mathlib
import Readings.LLogL
import ComparatorChallenges.FourierLLogL

/-! # Target O, family O17 (a.e. Fourier convergence in L log L): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: for `f` a.e.-strongly measurable for Mathlib's
`haarAddCircle` on `AddCircle (2π)` with `‖f‖ log(2 + ‖f‖)` integrable, a measurable null set off which the
symmetric sums `∑_{|k| ≤ N} fourierCoeff f k · fourier k x` tend to `f x`. Each reader's normalised measure
is proved equal to `haarAddCircle` (A: (ofReal 2π)⁻¹ • volume; B: ofReal (1/2π) • volume; C: haarAddCircle
itself), each reader's character equal to `fourier k` (A descends `t ↦ e^{ikt}` to the quotient), so their
coefficients and partial sums are the frozen ones; their L log L hypothesis (a lower integral < ∞) gives the
frozen integrability. Direction frozen ⇒ reading. -/

open MeasureTheory Filter Topology

namespace TargetO.LLogL

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem haar_eq_A : (ReaderA.μ : Measure (AddCircle (2 * Real.pi))) = AddCircle.haarAddCircle := by
  unfold ReaderA.μ
  rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul, ENNReal.inv_mul_cancel, one_smul]
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · exact ENNReal.ofReal_ne_top

theorem haar_eq_B : (ReaderB.μ : Measure (AddCircle (2 * Real.pi))) = AddCircle.haarAddCircle := by
  unfold ReaderB.μ
  rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul, ← ENNReal.ofReal_mul (by positivity),
    one_div, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_smul]

theorem expChar_eq (k : ℤ) (x : AddCircle (2 * Real.pi)) : ReaderA.expChar k x = fourier k x := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    unfold ReaderA.expChar
    rw [Function.Periodic.lift_coe, fourier_coe_apply]
    congr 1
    field_simp
    push_cast
    ring

/-- The frozen integrability from a reader's L log L hypothesis. -/
theorem integrable_of {f : AddCircle (2 * Real.pi) → ℂ}
    (hm : AEStronglyMeasurable f AddCircle.haarAddCircle)
    (hl : ∫⁻ x, ENNReal.ofReal (‖f x‖ * Real.log (2 + ‖f x‖)) ∂AddCircle.haarAddCircle < ⊤) :
    Integrable (fun x ↦ ‖f x‖ * Real.log (2 + ‖f x‖)) AddCircle.haarAddCircle := by
  have hcont : Continuous fun z : ℂ => ‖z‖ * Real.log (2 + ‖z‖) :=
    continuous_norm.mul (((continuous_const : Continuous fun _ : ℂ => (2 : ℝ)).add continuous_norm).log
      fun z => by have := norm_nonneg z; show (2 : ℝ) + ‖z‖ ≠ 0; exact ne_of_gt (by linarith))
  have hnn : ∀ x, 0 ≤ ‖f x‖ * Real.log (2 + ‖f x‖) := fun x =>
    mul_nonneg (norm_nonneg _) (Real.log_nonneg (by linarith [norm_nonneg (f x)]))
  refine ⟨hcont.comp_aestronglyMeasurable hm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
  exact hl

theorem A_thm : (type_of% @OAI.FourierLLogL.paperMain) → (type_of% @ReaderA.reading_thm_1_1) := by
  intro h f hf
  obtain ⟨hm, hl⟩ := hf
  rw [haar_eq_A] at hm hl
  obtain ⟨E, hE, h0, hc⟩ := h f hm (integrable_of hm hl)
  refine ⟨E, hE, by rw [haar_eq_A]; exact h0, fun x hx => ?_⟩
  have hx' : x ∉ E := hx.2
  convert hc x hx' using 2 with N
  unfold ReaderA.partialSum ReaderA.fourierCoeffT
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expChar_eq, haar_eq_A, fourierCoeff]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [expChar_eq, smul_eq_mul]
  ring

theorem B_thm : (type_of% @OAI.FourierLLogL.paperMain) → (type_of% @ReaderB.reading_thm_1_1) := by
  intro h f hf
  obtain ⟨hm, hl⟩ := hf
  rw [haar_eq_B] at hm hl
  obtain ⟨E, hE, h0, hc⟩ := h f hm (integrable_of hm hl)
  refine ⟨E, hE, by rw [haar_eq_B]; exact h0, fun x hx => ?_⟩
  convert hc x hx using 2 with N
  unfold ReaderB.S ReaderB.fhat ReaderB.e
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [haar_eq_B, fourierCoeff]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  ring

theorem C_thm : (type_of% @OAI.FourierLLogL.paperMain) →
    (type_of% @ReaderC.LLogL.reading_llogl_ae_convergence) := by
  intro h f hf
  obtain ⟨hm, hl⟩ := hf
  obtain ⟨E, hE, h0, hc⟩ := h f hm (integrable_of hm hl)
  refine ⟨E, hE, h0, fun x hx => ?_⟩
  convert hc x hx using 2 with N
  unfold ReaderC.LLogL.S ReaderC.LLogL.fhat
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourierCoeff]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  ring

end TargetO.LLogL

#print axioms TargetO.LLogL.A_thm
#print axioms TargetO.LLogL.B_thm
#print axioms TargetO.LLogL.C_thm
