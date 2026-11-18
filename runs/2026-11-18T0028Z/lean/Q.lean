import Checked.Trust.NecessityAP
import Checked.Cosmography.B1Separation

namespace Checked.Trust.NCAQ

open Set Filter Topology MeasureTheory Real
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

noncomputable def sa (s : ℝ) : ℝ := Real.sin s ^ (2 / 3 : ℝ)

theorem sin_pos_of (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) : 0 < Real.sin s :=
  Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])

theorem cos_pos_of (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) : 0 < Real.cos s :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

theorem sa_hasDerivAt (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) :
    HasDerivAt sa (Real.cos s * (2 / 3) * Real.sin s ^ ((2 / 3 : ℝ) - 1)) s :=
  (Real.hasDerivAt_sin s).rpow_const (Or.inl (sin_pos_of s h0 h1).ne')

theorem sa_pos (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) : 0 < sa s :=
  Real.rpow_pos_of_pos (sin_pos_of s h0 h1) _

theorem sa_hubble (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) :
    hubble sa s = 2 / 3 * (Real.cos s / Real.sin s) := by
  have hS := sin_pos_of s h0 h1
  unfold hubble
  rw [(sa_hasDerivAt s h0 h1).deriv]
  simp only [sa]
  rw [Real.rpow_sub hS, Real.rpow_one]
  have : 0 < Real.sin s ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hS _
  field_simp

theorem cube23 (x : ℝ) (hx : 0 < x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

theorem sa_z3 (t₀ s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) (h0' : 0 < t₀) (h1' : t₀ < π / 2) :
    (1 + redshift sa t₀ s) ^ 3 = Real.sin t₀ ^ 2 / Real.sin s ^ 2 := by
  have hS := sin_pos_of s h0 h1
  have hT := sin_pos_of t₀ h0' h1'
  unfold redshift
  rw [show 1 + (sa t₀ / sa s - 1) = sa t₀ / sa s by ring, div_pow]
  simp only [sa]
  rw [cube23 _ hS, cube23 _ hT]

/-- The flat law with `Ω cos² t₀ = 1` holds on `(0, t₀]`. -/
theorem sa_law (Ω t₀ : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hΩ : Ω * Real.cos t₀ ^ 2 = 1)
    (s : ℝ) (h0 : 0 < s) (hs : s ≤ t₀) :
    hubble sa s = hubble sa t₀ * √(Ω * (1 + redshift sa t₀ s) ^ 3 + 1 - Ω) := by
  have h1 : s < π / 2 := lt_of_le_of_lt hs h1'
  have hS := sin_pos_of s h0 h1
  have hT := sin_pos_of t₀ h0' h1'
  have hC := cos_pos_of s h0 h1
  have hCT := cos_pos_of t₀ h0' h1'
  rw [sa_z3 t₀ s h0 h1 h0' h1', sa_hubble s h0 h1, sa_hubble t₀ h0' h1']
  have e : Ω * (Real.sin t₀ ^ 2 / Real.sin s ^ 2) + 1 - Ω
      = (Real.sin t₀ / Real.cos t₀ * (Real.cos s / Real.sin s)) ^ 2 := by
    have hΩ' : Ω = 1 / Real.cos t₀ ^ 2 := by field_simp; linarith
    rw [hΩ']
    have := Real.sin_sq_add_cos_sq s
    have := Real.sin_sq_add_cos_sq t₀
    field_simp
    nlinarith
  rw [e, Real.sqrt_sq (by positivity)]
  field_simp

theorem sa_H0 (t₀ : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) : 0 < hubble sa t₀ := by
  rw [sa_hubble t₀ h0' h1']
  have := sin_pos_of t₀ h0' h1'; have := cos_pos_of t₀ h0' h1'; positivity

/-- A source time with `1 + z = Z` (any `Z ≥ 1`): `sin s = sin t₀ / Z^{3/2}`. -/
theorem sa_source (t₀ Z : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hZ : 1 ≤ Z) :
    let s := Real.arcsin (Real.sin t₀ / Z ^ (3 / 2 : ℝ))
    0 < s ∧ s ≤ t₀ ∧ redshift sa t₀ s = Z - 1 := by
  intro s
  have hT := sin_pos_of t₀ h0' h1'
  have hZ0 : 0 < Z := by linarith
  have hZp : 1 ≤ Z ^ (3 / 2 : ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hZp0 : 0 < Z ^ (3 / 2 : ℝ) := by linarith
  set y := Real.sin t₀ / Z ^ (3 / 2 : ℝ) with hy
  have hy0 : 0 < y := div_pos hT hZp0
  have hyT : y ≤ Real.sin t₀ := div_le_self hT.le hZp
  have hT1 : Real.sin t₀ ≤ 1 := Real.sin_le_one _
  have hs0 : 0 < s := Real.arcsin_pos.2 hy0
  have hsT : s ≤ t₀ := by
    have := Real.arcsin_le_arcsin hyT
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)] at this
  have hss : Real.sin s = y := Real.sin_arcsin (by linarith) (by linarith)
  refine ⟨hs0, hsT, ?_⟩
  have h1 : s < π / 2 := lt_of_le_of_lt hsT h1'
  have h3 := sa_z3 t₀ s hs0 h1 h0' h1'
  rw [hss, hy, div_pow, ← Real.rpow_natCast (Z ^ (3 / 2 : ℝ)), ← Real.rpow_mul hZ0.le] at h3
  norm_num at h3
  have hT2 : Real.sin t₀ ^ 2 ≠ 0 := by positivity
  rw [div_div_eq_mul_div, mul_div_assoc, mul_div_cancel₀ _ hT2] at h3
  have hpos : 0 < 1 + redshift sa t₀ s := by
    unfold redshift; rw [show 1 + (sa t₀ / sa s - 1) = sa t₀ / sa s by ring]
    exact div_pos (sa_pos t₀ h0' h1') (sa_pos s hs0 h1)
  have : 1 + redshift sa t₀ s = Z := by
    have h3' : (1 + redshift sa t₀ s) ^ 3 = Z ^ 3 := by
      rw [h3]
    exact (pow_left_inj₀ hpos.le hZ0.le (by norm_num)).1 h3'
  linarith


theorem sa_hyps (Ω t₀ t : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hΩ : Ω * Real.cos t₀ ^ 2 = 1)
    (ht0 : 0 < t) :
    (∀ s ∈ Set.Icc t t₀, 0 < sa s) ∧ (∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ sa s) ∧
      0 < hubble sa t₀ ∧
      (∀ s ∈ Set.Icc t t₀, hubble sa s = hubble sa t₀ * √(Ω * (1 + redshift sa t₀ s) ^ 3 + 1 - Ω)) :=
  ⟨fun s hs => sa_pos s (by linarith [hs.1]) (by linarith [hs.2]),
   fun s hs => (sa_hasDerivAt s (by linarith [hs.1]) (by linarith [hs.2])).differentiableAt,
   sa_H0 t₀ h0' h1',
   fun s hs => sa_law Ω t₀ h0' h1' hΩ s (by linarith [hs.1]) hs.2⟩

theorem int_bounds (Ω v₀ : ℝ) (hΩ : 1 ≤ Ω) (hv0 : 0 < v₀) (hv1 : v₀ ≤ 1) :
    0 ≤ ∫ v in v₀..1, 2 / √(Ω + (1 - Ω) * v ^ 6) ∧
      ∫ v in v₀..1, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ 2 * (1 - v₀) := by
  have hin : ∀ v ∈ Icc v₀ 1, 1 ≤ Ω + (1 - Ω) * v ^ 6 := by
    intro v hv
    have h6 : v ^ 6 ≤ 1 := pow_le_one₀ (by linarith [hv.1]) hv.2
    nlinarith
  have hc : ContinuousOn (fun v : ℝ => 2 / √(Ω + (1 - Ω) * v ^ 6)) (Icc v₀ 1) := by
    intro v hv
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_const.div
    · exact (by fun_prop : Continuous fun v : ℝ => Ω + (1 - Ω) * v ^ 6).continuousAt.sqrt
    · exact (Real.sqrt_pos.2 (by linarith [hin v hv])).ne'
  have hi : IntervalIntegrable (fun v : ℝ => 2 / √(Ω + (1 - Ω) * v ^ 6)) volume v₀ 1 :=
    hc.intervalIntegrable_of_Icc hv1
  constructor
  · exact intervalIntegral.integral_nonneg hv1 fun v _ => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · have := intervalIntegral.integral_mono_on hv1 hi (intervalIntegrable_const : IntervalIntegrable (fun _ => (2:ℝ)) volume v₀ 1)
      (fun v hv => by
        have h1 := hin v hv
        have : 1 ≤ √(Ω + (1 - Ω) * v ^ 6) := by
          simpa using Real.sqrt_le_sqrt h1
        rw [div_le_iff₀ (by linarith)]; nlinarith)
    simpa [mul_comm] using this

theorem five_logb_nonpos (d P : ℝ) (hd : 0 ≤ d) (hP : 0 < P) (h : d ≤ P) :
    5 * Real.logb 10 (d / P) ≤ 0 := by
  have : Real.logb 10 (d / P) ≤ 0 :=
    Real.logb_nonpos (by norm_num) (div_nonneg hd hP.le) ((div_le_one hP).2 h)
  linarith

theorem cos_pi_four_sq : 2 * Real.cos (π / 4) ^ 2 = 1 := by
  rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem H0_two : hubble sa (π / 4) = 2 / 3 := by
  rw [sa_hubble _ (by positivity) (by linarith [Real.pi_pos]), Real.cos_pi_div_four,
    Real.sin_pi_div_four, div_self (by positivity)]; ring

/-- Ω = 2, observation at `π/4`, a source at `1 + z = Z`: the luminosity distance is at most
`(1 + z) · (3/2) · 2 (1 − 1/√Z)` and the ΛCDM-implied cubic is `(3/2) Qc 2 (ln Z)`. -/
theorem two_bounds (Z : ℝ) (hZ : 1 ≤ Z) :
    let t := Real.arcsin (Real.sin (π / 4) / Z ^ (3 / 2 : ℝ))
    0 < t ∧ t ≤ π / 4 ∧ redshift sa (π / 4) t = Z - 1 ∧
      0 ≤ lumDistFlat sa (π / 4) t ∧
      lumDistFlat sa (π / 4) t ≤ Z * (3 / 2) * (2 * (1 - √(1 / Z))) := by
  intro t
  have hpi : 0 < π / 4 := by positivity
  have hpi2 : π / 4 < π / 2 := by linarith [Real.pi_pos]
  obtain ⟨ht0, htt, hz⟩ := sa_source (π / 4) Z hpi hpi2 hZ
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps 2 (π / 4) t hpi hpi2 cos_pi_four_sq ht0
  have hbr := bridge 2 (by norm_num) sa t (π / 4) htt hp hd hH₀ hH
  have hr : sa t / sa (π / 4) = 1 / Z := by
    rw [ratio_of_z sa t (π / 4) (Z - 1) (hp t ⟨le_rfl, htt⟩) (hp _ ⟨htt, le_rfl⟩) hz]; ring_nf
  rw [hr, hz, H0_two] at hbr
  have hZ0 : 0 < Z := by linarith
  have hv0 : 0 < √(1 / Z) := Real.sqrt_pos.2 (by positivity)
  have hv1 : √(1 / Z) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact (div_le_one hZ0).2 hZ
  obtain ⟨hI0, hI⟩ := int_bounds 2 _ (by norm_num) hv0 hv1
  refine ⟨ht0, htt, hz, ?_, ?_⟩
  · rw [hbr]; apply mul_nonneg _ hI0; rw [show 1 + (Z - 1) = Z by ring]; positivity
  · rw [hbr, show 1 + (Z - 1) = Z by ring, show Z / (2 / 3) = Z * (3 / 2) by ring]
    exact mul_le_mul_of_nonneg_left hI (by positivity)

theorem Qc_two (u : ℝ) : Qc 2 u = u + 5 / 3 * u ^ 3 := by unfold Qc; ring

/-- Without `Ω ≤ 2/5`: at `Ω = 2` the cubic at `z = 3` overestimates the distance. -/
theorem cubic_misses_z3_h2 : necessity% Checked.Cosmography.B1.cubic_misses_z3 2 := by
  have hpi : 0 < π / 4 := by positivity
  have hpi2 : π / 4 < π / 2 := by linarith [Real.pi_pos]
  obtain ⟨ht0, htt, hz, hd0, hdl⟩ := two_bounds 4 (by norm_num)
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps 2 (π / 4) _ hpi hpi2 cos_pi_four_sq ht0
  have hz' : redshift sa (π / 4) (Real.arcsin (Real.sin (π / 4) / (4:ℝ) ^ (3 / 2 : ℝ))) = 3 := by
    rw [hz]; norm_num
  refine ⟨2, by norm_num, sa, _, π / 4, htt, hp, hd, hH₀, hH, hz', ?_⟩
  rintro ⟨-, hB⟩
  rw [hz', poly_eq 2 _ 3 (by rw [H0_two]; norm_num), H0_two, Qc_two, log4] at hB
  have h4 : √(1 / (4:ℝ)) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at hdl
  have hl := Real.log_two_gt_d9
  have hu : (1.38 : ℝ) ≤ 2 * Real.log 2 := by linarith
  have hu3 := pow_le_pow_left₀ (by norm_num) hu 3
  have hQ : 6 < (2 * Real.log 2 + 5 / 3 * (2 * Real.log 2) ^ 3) / (2 / 3) := by
    rw [lt_div_iff₀ (by norm_num)]; norm_num at hu3 ⊢; linarith
  have := five_logb_nonpos _ ((2 * Real.log 2 + 5 / 3 * (2 * Real.log 2) ^ 3) / (2 / 3)) hd0
    (by linarith) (by linarith)
  linarith

/-- Without `Ω ≤ 2/5`: at `Ω = 2` the cubic at `z = 7` overestimates the distance. -/
theorem cubic_misses_z7_h2 : necessity% Checked.Cosmography.B1.cubic_misses_z7 2 := by
  have hpi : 0 < π / 4 := by positivity
  have hpi2 : π / 4 < π / 2 := by linarith [Real.pi_pos]
  obtain ⟨ht0, htt, hz, hd0, hdl⟩ := two_bounds 8 (by norm_num)
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps 2 (π / 4) _ hpi hpi2 cos_pi_four_sq ht0
  have hz' : redshift sa (π / 4) (Real.arcsin (Real.sin (π / 4) / (8:ℝ) ^ (3 / 2 : ℝ))) = 7 := by
    rw [hz]; norm_num
  refine ⟨2, by norm_num, sa, _, π / 4, htt, hp, hd, hH₀, hH, hz', ?_⟩
  rintro ⟨-, hB⟩
  rw [hz', poly_eq 2 _ 7 (by rw [H0_two]; norm_num), H0_two, Qc_two, log8] at hB
  have h8 : (1 / 3 : ℝ) ≤ √(1 / (8:ℝ)) := by
    rw [show (1 / 3 : ℝ) = √((1 / 3) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hdl' : lumDistFlat sa (π / 4) (Real.arcsin (Real.sin (π / 4) / (8:ℝ) ^ (3 / 2 : ℝ))) ≤ 16 := by
    nlinarith
  have hl := Real.log_two_gt_d9
  have hu : (2.07 : ℝ) ≤ 3 * Real.log 2 := by linarith
  have hu3 := pow_le_pow_left₀ (by norm_num) hu 3
  have hQ : 16 < (3 * Real.log 2 + 5 / 3 * (3 * Real.log 2) ^ 3) / (2 / 3) := by
    rw [lt_div_iff₀ (by norm_num)]; norm_num at hu3 ⊢; linarith
  have := five_logb_nonpos _ ((3 * Real.log 2 + 5 / 3 * (3 * Real.log 2) ^ 3) / (2 / 3)) hd0
    (by linarith) (by linarith)
  linarith


/-! ## Generic closed-form model with `Ω > 1` and interval bounds of the integrand -/

/-- Observation time with `Ω cos² t₀ = 1`. -/
noncomputable def tO (Ω : ℝ) : ℝ := Real.arccos (1 / √Ω)

/-- Source time with `1 + z = Z`. -/
noncomputable def tS (Ω Z : ℝ) : ℝ := Real.arcsin (Real.sin (tO Ω) / Z ^ (3 / 2 : ℝ))

theorem tO_props (Ω : ℝ) (hΩ : 1 < Ω) :
    0 < tO Ω ∧ tO Ω < π / 2 ∧ Ω * Real.cos (tO Ω) ^ 2 = 1 := by
  have hs : 1 < √Ω := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) hΩ
  have hx0 : 0 < 1 / √Ω := by positivity
  have hx1 : 1 / √Ω < 1 := by rw [div_lt_one (by positivity)]; exact hs
  refine ⟨Real.arccos_pos.2 hx1, Real.arccos_lt_pi_div_two.2 hx0, ?_⟩
  rw [tO, Real.cos_arccos (by linarith) hx1.le, div_pow, Real.sq_sqrt (by linarith)]
  field_simp

theorem tS_props (Ω Z : ℝ) (hΩ : 1 < Ω) (hZ : 1 ≤ Z) :
    0 < tS Ω Z ∧ tS Ω Z ≤ tO Ω ∧ redshift sa (tO Ω) (tS Ω Z) = Z - 1 := by
  obtain ⟨h0, h1, -⟩ := tO_props Ω hΩ
  exact sa_source (tO Ω) Z h0 h1 hZ

theorem tS_anti (Ω Z₁ Z₂ : ℝ) (hΩ : 1 < Ω) (hZ : 1 ≤ Z₁) (h12 : Z₁ ≤ Z₂) :
    tS Ω Z₂ ≤ tS Ω Z₁ := by
  obtain ⟨h0, h1, -⟩ := tO_props Ω hΩ
  have hT := sin_pos_of _ h0 h1
  apply Real.arcsin_le_arcsin
  apply div_le_div_of_nonneg_left hT.le (Real.rpow_pos_of_pos (by linarith) _)
  exact Real.rpow_le_rpow (by linarith) h12 (by norm_num)

/-- The bridge in the model: `d_L = Z/H₀ · ∫_{1/√Z}^1 g`. -/
theorem sa_dL (Ω Z : ℝ) (hΩ : 1 < Ω) (hZ : 1 ≤ Z) :
    lumDistFlat sa (tO Ω) (tS Ω Z) = Z / hubble sa (tO Ω) *
      ∫ v in √(1 / Z)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  obtain ⟨h0, h1, hc⟩ := tO_props Ω hΩ
  obtain ⟨ht0, htt, hz⟩ := tS_props Ω Z hΩ hZ
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps Ω (tO Ω) (tS Ω Z) h0 h1 hc ht0
  have hbr := bridge Ω (by linarith) sa _ _ htt hp hd hH₀ hH
  rw [ratio_of_z sa _ _ (Z - 1) (hp _ ⟨le_rfl, htt⟩) (hp _ ⟨htt, le_rfl⟩) hz, hz] at hbr
  rw [hbr]; ring_nf

theorem g_mono (Ω v w : ℝ) (hΩ : 1 ≤ Ω) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ 1) :
    2 / √(Ω + (1 - Ω) * v ^ 6) ≤ 2 / √(Ω + (1 - Ω) * w ^ 6) := by
  have hw6 : w ^ 6 ≤ 1 := pow_le_one₀ (by linarith) hw
  have h66 : v ^ 6 ≤ w ^ 6 := pow_le_pow_left₀ hv hvw 6
  have hpw : 0 < Ω + (1 - Ω) * w ^ 6 := by nlinarith
  apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hpw)
  apply Real.sqrt_le_sqrt; nlinarith

theorem g_ge (Ω v : ℝ) (hΩ : 1 ≤ Ω) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    2 / √Ω ≤ 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  have h6 : 0 ≤ v ^ 6 := by positivity
  have h61 : v ^ 6 ≤ 1 := pow_le_one₀ hv hv1
  have hp : 0 < Ω + (1 - Ω) * v ^ 6 := by nlinarith
  apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hp)
  apply Real.sqrt_le_sqrt; nlinarith

theorem g_one (Ω : ℝ) : 2 / √(Ω + (1 - Ω) * (1:ℝ) ^ 6) = 2 := by norm_num

theorem g_cont (Ω p q : ℝ) (hΩ : 1 ≤ Ω) (hp : 0 ≤ p) (hq : q ≤ 1) :
    ContinuousOn (fun v : ℝ => 2 / √(Ω + (1 - Ω) * v ^ 6)) (Icc p q) := by
  intro v hv
  have h6 : v ^ 6 ≤ 1 := pow_le_one₀ (by linarith [hv.1]) (by linarith [hv.2])
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.div
  · exact (by fun_prop : Continuous fun v : ℝ => Ω + (1 - Ω) * v ^ 6).continuousAt.sqrt
  · exact (Real.sqrt_pos.2 (by nlinarith)).ne'

theorem int_piece (Ω p q : ℝ) (hΩ : 1 ≤ Ω) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    (q - p) * (2 / √(Ω + (1 - Ω) * p ^ 6)) ≤ ∫ v in p..q, 2 / √(Ω + (1 - Ω) * v ^ 6) ∧
      ∫ v in p..q, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ (q - p) * (2 / √(Ω + (1 - Ω) * q ^ 6)) := by
  have hi : IntervalIntegrable (fun v : ℝ => 2 / √(Ω + (1 - Ω) * v ^ 6)) volume p q :=
    (g_cont Ω p q hΩ hp hq).intervalIntegrable_of_Icc hpq
  constructor
  · have := intervalIntegral.integral_mono_on hpq
      (intervalIntegrable_const : IntervalIntegrable (fun _ => 2 / √(Ω + (1 - Ω) * p ^ 6)) volume p q) hi
      (fun v hv => g_mono Ω p v hΩ hp hv.1 (le_trans hv.2 hq))
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  · have := intervalIntegral.integral_mono_on hpq hi
      (intervalIntegrable_const : IntervalIntegrable (fun _ => 2 / √(Ω + (1 - Ω) * q ^ 6)) volume p q)
      (fun v hv => g_mono Ω v q hΩ (le_trans hp hv.1) hv.2 hq)
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this

theorem int_split (Ω p q : ℝ) (hΩ : 1 ≤ Ω) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ∫ v in p..1, 2 / √(Ω + (1 - Ω) * v ^ 6) =
      (∫ v in p..q, 2 / √(Ω + (1 - Ω) * v ^ 6)) + ∫ v in q..1, 2 / √(Ω + (1 - Ω) * v ^ 6) :=
  (intervalIntegral.integral_add_adjacent_intervals
    ((g_cont Ω p q hΩ hp hq).intervalIntegrable_of_Icc hpq)
    ((g_cont Ω q 1 hΩ (le_trans hp hpq) le_rfl).intervalIntegrable_of_Icc hq)).symm

theorem sqrt8_bounds : (35 / 100 : ℝ) ≤ √(1 / 8) ∧ √(1 / 8 : ℝ) ≤ 354 / 1000 := by
  constructor
  · rw [show (35 / 100 : ℝ) = √((35 / 100) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [show (354 / 1000 : ℝ) = √((354 / 1000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)

theorem sqrt4 : √(1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `J₇ ≤ (2 − 2 v₇) J₃` and `J₇ ≥ J₃ + (1/2 − v₇) g(v₇)` for every `Ω ≥ 1`, with
`J_Z = ∫_{1/√Z}^1 g`. -/
theorem J73 (Ω : ℝ) (hΩ : 1 ≤ Ω) :
    let J3 := ∫ v in √(1 / 4 : ℝ)..1, 2 / √(Ω + (1 - Ω) * v ^ 6)
    let J7 := ∫ v in √(1 / 8 : ℝ)..1, 2 / √(Ω + (1 - Ω) * v ^ 6)
    0 < J3 ∧ J3 ≤ 1 ∧ J7 ≤ (2 - 2 * (35 / 100)) * J3 ∧
      J3 + (1 / 2 - 354 / 1000) * (2 / √Ω) ≤ J7 := by
  intro J3 J7
  obtain ⟨h35, h354⟩ := sqrt8_bounds
  have hs := int_split Ω (√(1 / 8)) (1 / 2) hΩ (Real.sqrt_nonneg _) (by linarith) (by norm_num)
  have hJ3 : J3 = ∫ v in (1 / 2 : ℝ)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by simp only [J3, sqrt4]
  obtain ⟨hA, hB⟩ := int_piece Ω (1 / 2) 1 hΩ (by norm_num) (by norm_num) le_rfl
  obtain ⟨hC, hD⟩ := int_piece Ω (√(1 / 8)) (1 / 2) hΩ (Real.sqrt_nonneg _) (by linarith) (by norm_num)
  rw [g_one] at hB
  have hc0 : 0 < 2 / √(Ω + (1 - Ω) * (1 / 2 : ℝ) ^ 6) := by
    have := g_ge Ω (1 / 2) hΩ (by norm_num) (by norm_num); have : 0 < 2 / √Ω := by positivity
    linarith
  have hg7 := g_ge Ω (√(1 / 8)) hΩ (Real.sqrt_nonneg _) (by linarith)
  have hsq : 0 < 2 / √Ω := by have : 0 < Ω := by linarith
                              positivity
  refine ⟨by rw [hJ3]; nlinarith, by rw [hJ3]; linarith, ?_, ?_⟩
  · show J7 ≤ _; simp only [J7]; rw [hs, ← hJ3]
    nlinarith
  · show _ ≤ J7; simp only [J7]; rw [hs, ← hJ3]
    nlinarith

theorem logb_div' (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    5 * Real.logb 10 x - 5 * Real.logb 10 y = 5 * Real.logb 10 (x / y) := by
  rw [Real.logb_div hx.ne' hy.ne']; ring

/-- Without `Ω ≤ 2/5`: at `Ω = 2` the miss at `z = 7` is below the miss at `z = 3`. -/
theorem cubic_shape_miss_h2 : necessity% Checked.Cosmography.B1.cubic_shape_miss 2 := by
  have hΩ : (1:ℝ) < 2 := by norm_num
  obtain ⟨h0, h1, hc⟩ := tO_props 2 hΩ
  obtain ⟨ht7, h7O, hz7⟩ := tS_props 2 8 hΩ (by norm_num)
  obtain ⟨ht3, h3O, hz3⟩ := tS_props 2 4 hΩ (by norm_num)
  have h73 := tS_anti 2 4 8 hΩ (by norm_num) (by norm_num)
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps 2 (tO 2) (tS 2 8) h0 h1 hc ht7
  refine ⟨2, by norm_num, sa, tS 2 8, tS 2 4, tO 2, h73, h3O, hp, hd, hH₀, hH,
    by rw [hz3]; norm_num, by rw [hz7]; norm_num, ?_⟩
  rw [hz3, hz7, show (8:ℝ) - 1 = 7 by norm_num, show (4:ℝ) - 1 = 3 by norm_num,
    poly_eq 2 _ 7 hH₀.ne', poly_eq 2 _ 3 hH₀.ne', Qc_two, Qc_two, log8, log4,
    sa_dL 2 8 hΩ (by norm_num), sa_dL 2 4 hΩ (by norm_num)]
  obtain ⟨hJ3p, -, hJ7u, hJ7l⟩ := J73 2 (by norm_num)
  have hs2 : (0:ℝ) < 2 / √2 := by positivity
  set J3 := ∫ v in √(1 / 4 : ℝ)..1, 2 / √(2 + (1 - 2) * v ^ 6)
  set J7 := ∫ v in √(1 / 8 : ℝ)..1, 2 / √(2 + (1 - 2) * v ^ 6)
  set H := hubble sa (tO 2)
  set l := Real.log 2
  have hl := Real.log_two_gt_d9
  have hJ7p : 0 < J7 := by nlinarith
  have hHp : 0 < H := hH₀
  have hQ3 : 0 < 2 * l + 5 / 3 * (2 * l) ^ 3 := by positivity
  have hQ7 : 0 < 3 * l + 5 / 3 * (3 * l) ^ 3 := by positivity
  have e7 : 8 / H * J7 / ((3 * l + 5 / 3 * (3 * l) ^ 3) / H) = 8 * J7 / (3 * l + 5 / 3 * (3 * l) ^ 3) := by
    field_simp
  have e3 : 4 / H * J3 / ((2 * l + 5 / 3 * (2 * l) ^ 3) / H) = 4 * J3 / (2 * l + 5 / 3 * (2 * l) ^ 3) := by
    field_simp
  rw [e7, e3]
  have hx7 : 0 < 8 * J7 / (3 * l + 5 / 3 * (3 * l) ^ 3) := by positivity
  have hx3 : 0 < 4 * J3 / (2 * l + 5 / 3 * (2 * l) ^ 3) := by positivity
  rw [logb_div' _ _ hx7 hx3, not_lt]
  have hle : 8 * J7 / (3 * l + 5 / 3 * (3 * l) ^ 3) / (4 * J3 / (2 * l + 5 / 3 * (2 * l) ^ 3)) ≤ 1 := by
    rw [div_le_one hx3, div_le_div_iff₀ hQ7 hQ3]
    have hl2 : (0.69 : ℝ) ≤ l := by linarith
    have key : 8 * ((2 - 2 * (35 / 100)) * J3) * (2 * l + 5 / 3 * (2 * l) ^ 3) ≤
        4 * J3 * (3 * l + 5 / 3 * (3 * l) ^ 3) := by
      have e : 4 * J3 * (3 * l + 5 / 3 * (3 * l) ^ 3) - 8 * ((2 - 2 * (35 / 100)) * J3) *
          (2 * l + 5 / 3 * (2 * l) ^ 3) = J3 * l * (-(44 / 5) + 124 / 3 * l ^ 2) := by
        ring
      rw [← sub_nonneg, e]
      apply mul_nonneg (mul_nonneg hJ3p.le (by linarith))
      nlinarith
    calc 8 * J7 * (2 * l + 5 / 3 * (2 * l) ^ 3)
        ≤ 8 * ((2 - 2 * (35 / 100)) * J3) * (2 * l + 5 / 3 * (2 * l) ^ 3) := by gcongr
      _ ≤ 4 * J3 * (3 * l + 5 / 3 * (3 * l) ^ 3) := key
  have := Real.logb_nonpos (b := 10) (by norm_num) (by positivity) hle
  linarith


theorem Qc_32 (u : ℝ) : Qc (3 / 2) u = u + 3 / 8 * u ^ 2 + 67 / 96 * u ^ 3 := by unfold Qc; ring

theorem log10_gt : (2.27 : ℝ) < Real.log 10 := by
  have h8 : Real.log 10 = Real.log 8 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h8' : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h54 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 5 / 4 by norm_num)
  have := Real.log_two_gt_d9
  norm_num at h54
  linarith

theorem logb_small (x : ℝ) (h1 : 98 / 100 ≤ x) (h2 : x ≤ 104 / 100) :
    |5 * Real.logb 10 x| ≤ 1 / 10 := by
  have hx : 0 < x := by linarith
  have hl10 := log10_gt
  have hu := Real.log_le_sub_one_of_pos hx
  have hd := Real.one_sub_inv_le_log_of_pos hx
  have hinv : x⁻¹ ≤ 100 / 98 := by rw [inv_le_comm₀ hx (by norm_num)]; norm_num; linarith
  rw [abs_le, Real.logb]
  constructor
  · rw [show -(1 / 10 : ℝ) = 5 * (-(1 / 50)) by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [show (1 / 10 : ℝ) = 5 * (1 / 50) by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [div_le_iff₀ (by linarith)]; nlinarith

/-- At `Ω = 3/2` the ΛCDM-implied cubic misses the exact distance modulus at `z = 3` and at
`z = 7` by amounts within 0.1 mag of each other. -/
theorem misses_32 :
    let Ω : ℝ := 3 / 2
    let H := hubble sa (tO Ω)
    |5 * Real.logb 10 (lumDistFlat sa (tO Ω) (tS Ω 8) / logPolyDL3 (lusA2 Ω) (lusA3 Ω) H 7) -
      5 * Real.logb 10 (lumDistFlat sa (tO Ω) (tS Ω 4) / logPolyDL3 (lusA2 Ω) (lusA3 Ω) H 3)| ≤ 1 / 10 := by
  intro Ω H
  have hΩ : (1:ℝ) < 3 / 2 := by norm_num
  obtain ⟨h0, h1, hc⟩ := tO_props (3 / 2) hΩ
  have hHp : 0 < H := sa_H0 _ h0 h1
  rw [poly_eq _ _ 7 hHp.ne', poly_eq _ _ 3 hHp.ne', Qc_32, Qc_32, log8, log4,
    sa_dL (3 / 2) 8 hΩ (by norm_num), sa_dL (3 / 2) 4 hΩ (by norm_num)]
  obtain ⟨hJ3p, hJ31, hJ7u, hJ7l⟩ := J73 (3 / 2) (by norm_num)
  have hsq : √(3 / 2 : ℝ) ≤ 12248 / 10000 := by
    rw [show (12248 / 10000 : ℝ) = √((12248 / 10000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hg : (16329 / 10000 : ℝ) ≤ 2 / √(3 / 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  set J3 := ∫ v in √(1 / 4 : ℝ)..1, 2 / √(3 / 2 + (1 - 3 / 2) * v ^ 6)
  set J7 := ∫ v in √(1 / 8 : ℝ)..1, 2 / √(3 / 2 + (1 - 3 / 2) * v ^ 6)
  set l := Real.log 2
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  have hJ7a : (1 + 2384 / 10000) * J3 ≤ J7 := by nlinarith
  have hJ7p : 0 < J7 := by nlinarith
  set Q3 := 2 * l + 3 / 8 * (2 * l) ^ 2 + 67 / 96 * (2 * l) ^ 3
  set Q7 := 3 * l + 3 / 8 * (3 * l) ^ 2 + 67 / 96 * (3 * l) ^ 3
  have hQ3 : 0 < Q3 := by positivity
  have hQ7 : 0 < Q7 := by positivity
  have e7 : 8 / H * J7 / (Q7 / H) = 8 * J7 / Q7 := by field_simp
  have e3 : 4 / H * J3 / (Q3 / H) = 4 * J3 / Q3 := by field_simp
  rw [e7, e3]
  have hx7 : 0 < 8 * J7 / Q7 := by positivity
  have hx3 : 0 < 4 * J3 / Q3 := by positivity
  rw [logb_div' _ _ hx7 hx3]
  have hr : 8 * J7 / Q7 / (4 * J3 / Q3) = 2 * J7 * Q3 / (J3 * Q7) := by field_simp; ring
  rw [hr]
  have hl1 : (0.6931 : ℝ) ≤ l := by linarith
  have hl2 : l ≤ (0.6932 : ℝ) := by linarith
  have hlo : 98 / 100 * Q7 ≤ 2 * (1 + 2384 / 10000) * Q3 := by
    simp only [Q3, Q7]; nlinarith [mul_pos (show (0:ℝ) < l by linarith) (show (0:ℝ) < l by linarith)]
  have hhi : 2 * (2 - 2 * (35 / 100)) * Q3 ≤ 104 / 100 * Q7 := by
    simp only [Q3, Q7]; nlinarith [mul_pos (show (0:ℝ) < l by linarith) (show (0:ℝ) < l by linarith)]
  apply logb_small
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hJ7a (show (0:ℝ) ≤ 2 * Q3 by positivity),
      mul_le_mul_of_nonneg_left hlo hJ3p.le]
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hJ7u (show (0:ℝ) ≤ 2 * Q3 by positivity),
      mul_le_mul_of_nonneg_left hhi hJ3p.le]

/-- The common data of the two `Ω = 3/2` witnesses. -/
theorem data_32 :
    let Ω : ℝ := 3 / 2
    1 / 5 ≤ Ω ∧ tS Ω 8 ≤ tS Ω 4 ∧ tS Ω 4 ≤ tO Ω ∧
      (∀ s ∈ Set.Icc (tS Ω 8) (tO Ω), 0 < sa s) ∧
      (∀ s ∈ Set.Icc (tS Ω 8) (tO Ω), DifferentiableAt ℝ sa s) ∧ 0 < hubble sa (tO Ω) ∧
      (∀ s ∈ Set.Icc (tS Ω 8) (tO Ω),
        hubble sa s = hubble sa (tO Ω) * √(Ω * (1 + redshift sa (tO Ω) s) ^ 3 + 1 - Ω)) ∧
      redshift sa (tO Ω) (tS Ω 4) = 3 ∧ redshift sa (tO Ω) (tS Ω 8) = 7 ∧
      0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble sa (tO Ω)) 3 ∧
      0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble sa (tO Ω)) 7 := by
  intro Ω
  have hΩ : (1:ℝ) < 3 / 2 := by norm_num
  obtain ⟨h0, h1, hc⟩ := tO_props (3 / 2) hΩ
  obtain ⟨ht7, -, hz7⟩ := tS_props (3 / 2) 8 hΩ (by norm_num)
  obtain ⟨-, h3O, hz3⟩ := tS_props (3 / 2) 4 hΩ (by norm_num)
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps (3 / 2) (tO (3 / 2)) (tS (3 / 2) 8) h0 h1 hc ht7
  have hl := Real.log_two_gt_d9
  refine ⟨by norm_num, tS_anti _ 4 8 hΩ (by norm_num) (by norm_num), h3O, hp, hd, hH₀, hH,
    by rw [hz3]; norm_num, by rw [hz7]; norm_num, ?_, ?_⟩
  · rw [poly_eq _ _ 3 hH₀.ne', Qc_32, log4]; apply div_pos _ hH₀; positivity
  · rw [poly_eq _ _ 7 hH₀.ne', Qc_32, log8]; apply div_pos _ hH₀; positivity

theorem half_abs (x y : ℝ) (h : |y - x| ≤ 1 / 10) :
    |x - (x + y) / 2| ≤ 1 / 20 ∧ |y - (x + y) / 2| ≤ 1 / 20 := by
  rw [abs_le] at h ⊢; rw [abs_le]; constructor <;> constructor <;> linarith [h.1, h.2]

/-- Without `Ω ≤ 2/5`: at `Ω = 3/2` the ΛCDM-implied cubic itself matches both distance moduli
within 0.05 mag up to a common offset, at distance zero from the ΛCDM-implied point. -/
theorem cubic_separation_h2 : necessity% Checked.Cosmography.B1Sep.cubic_separation 2 := by
  obtain ⟨h1, h73, h3O, hp, hd, hH₀, hH, hz3, hz7, hp3, hp7⟩ := data_32
  have hm := misses_32
  simp only at hm
  obtain ⟨hm3, hm7⟩ := half_abs _ _ hm
  refine ⟨3 / 2, h1, sa, tS (3 / 2) 8, tS (3 / 2) 4, tO (3 / 2), h73, h3O, hp, hd, hH₀, hH, hz3, hz7,
    lusA2 (3 / 2), lusA3 (3 / 2), hubble sa (tO (3 / 2)), _, hH₀, by rwa [hz3], by rwa [hz7],
    by rw [hz3]; exact hm3, by rw [hz7]; exact hm7, ?_⟩
  simp only [sub_self]; norm_num

/-- Without `Ω ≤ 2/5`: the same `Ω = 3/2` data, where the ΛCDM-implied point is not on the
strict side of the direction line. -/
theorem cubic_direction_h2 : necessity% Checked.Cosmography.B1Sep.cubic_direction 2 := by
  obtain ⟨h1, h73, h3O, hp, hd, hH₀, hH, hz3, hz7, hp3, hp7⟩ := data_32
  have hm := misses_32
  simp only at hm
  obtain ⟨hm3, hm7⟩ := half_abs _ _ hm
  refine ⟨3 / 2, h1, sa, tS (3 / 2) 8, tS (3 / 2) 4, tO (3 / 2), h73, h3O, hp, hd, hH₀, hH, hz3, hz7,
    lusA2 (3 / 2), lusA3 (3 / 2), hubble sa (tO (3 / 2)), _, hH₀, by rwa [hz3], by rwa [hz7],
    by rw [hz3]; exact hm3, by rw [hz7]; exact hm7, ?_⟩
  simp

end Checked.Trust.NCAQ
