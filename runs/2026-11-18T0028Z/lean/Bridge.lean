import Checked.Trust.NecessityAP

namespace Checked.Trust.NCAQ

open Set Filter Topology MeasureTheory
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

theorem inner_pos0 (Ω v : ℝ) (hΩ₀ : 0 ≤ Ω) (hv : 0 < v) (hv1 : v ≤ 1) :
    0 < Ω + (1 - Ω) * v ^ 6 := by
  have h6 : v ^ 6 ≤ 1 := pow_le_one₀ hv.le hv1
  have : 0 < v ^ 6 := by positivity
  nlinarith [mul_nonneg hΩ₀ (sub_nonneg.2 h6)]

/-- Under the flat law the scale factor never exceeds its value at the observation time
on the interval: the Hubble rate is a square root times `H₀ > 0`, so `a' ≥ 0`. -/
theorem le_a0 (Ω : ℝ) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    ∀ s ∈ Set.Icc t t₀, a s ≤ a t₀ := by
  have hmono : MonotoneOn a (Icc t t₀) := by
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
  intro s hs
  exact hmono hs ⟨htt, le_rfl⟩ hs.2

/-- The bridge without `Ω ≤ 1`. -/
theorem bridge (Ω : ℝ) (hΩ₀ : 0 ≤ Ω)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    lumDistFlat a t₀ t = (1 + redshift a t₀ t) / hubble a t₀ *
      ∫ v in √(a t / a t₀)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  have hle := le_a0 Ω a t t₀ htt hpos hdiff hH₀ hH
  set a₀ := a t₀ with ha₀def
  set H₀ := hubble a t₀ with hH₀def
  have ha₀ : 0 < a₀ := hpos t₀ ⟨htt, le_rfl⟩
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
  have hG : ∀ x, 0 < x → x ≤ 1 → HasDerivAt G (g x) x := by
    intro x hx hx1
    have hsub : uIcc (1:ℝ) x ⊆ U := by
      intro y hy
      rw [uIcc_of_ge hx1] at hy
      have hy0 : 0 < y := lt_of_lt_of_le hx hy.1
      exact ⟨hy0, inner_pos0 Ω y hΩ₀ hy0 hy.2⟩
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
      exact hle s hs
    have hW2 : a s = W s ^ 2 * a₀ := by
      simp only [hWdef]; rw [Real.sq_sqrt hr.le]; field_simp
    have hd : HasDerivAt W ((deriv a s / a₀) / (2 * √(a s / a₀))) s :=
      ((hdiff s hs).hasDerivAt.div_const a₀).sqrt hr.ne'
    have hc := ((hG (W s) hWs hW1).comp s hd).div_const (H₀ * a₀)
    have hin := inner_pos0 Ω (W s) hΩ₀ hWs hW1
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

theorem lumDistFlat_flatLCDM_r2 : dropped% Checked.Cosmography.B1.lumDistFlat_flatLCDM 2 :=
  fun Ω h0 a t t₀ htt hp hd hH₀ hH => bridge Ω h0 a t t₀ htt hp hd hH₀ hH

end Checked.Trust.NCAQ
#print axioms Checked.Trust.NCAQ.lumDistFlat_flatLCDM_r2
