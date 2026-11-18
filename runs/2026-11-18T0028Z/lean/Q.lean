import Checked.Trust.NecessityAP

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

end Checked.Trust.NCAQ
