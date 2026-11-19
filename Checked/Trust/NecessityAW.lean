import Checked.Cosmography.FRCosmo
import Checked.Trust.NecessityAQ
import Checked.Trust.NonVacuity

/-! Hypothesis necessity for three statements of `Checked.Cosmography.FRCosmo` (run 2026-11-19T0028Z).
`exists_LCDM_model` gives, for a matter density strictly between zero and one, a flat model with matter
and a cosmological constant that satisfies every condition of the metric F(R) setting with F(R) equal
to R plus a constant. Both of its bounds are REDUNDANT (each alone): at density one the Einstein–de
Sitter scale factor, above one the closed-form model of `Checked.Trust.NecessityAQ` (the sine of the time
to the power two thirds, a negative cosmological constant), at density zero de Sitter (the exponential)
and below zero the hyperbolic cosine to the power two thirds satisfy the same conditions (`sa_model`,
`eds_model`, `exp_model`, `ca_model`). With the last two, the lower density bound of the refutations
`printedF0Mul_false_at` and `printedF0_false_at` is REDUNDANT as well: the printed relation fails in
those models for the same algebraic reason as in the statement (a factor two minus the density times a
positive quadratic). Their upper bound stays open: at density two that factor vanishes. -/

namespace Checked.Trust.NecessityAW
open Real Filter Topology Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.FRCosmo Checked.Trust.NCAQ

theorem sa_law' (Ω t₀ : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hΩ : Ω * Real.cos t₀ ^ 2 = 1)
    (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) :
    hubble sa s = hubble sa t₀ * √(Ω * (1 + redshift sa t₀ s) ^ 3 + 1 - Ω) := by
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

theorem sa_flat (Ω t₀ : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hΩ : Ω * Real.cos t₀ ^ 2 = 1) :
    IsFlatLCDM Ω sa t₀ := by
  refine ⟨sa_H0 t₀ h0' h1', ?_⟩
  filter_upwards [Ioo_mem_nhds h0' h1'] with s hs
  exact ⟨sa_pos s hs.1 hs.2, (sa_hasDerivAt s hs.1 hs.2).differentiableAt,
    sa_law' Ω t₀ h0' h1' hΩ s hs.1 hs.2⟩

theorem deriv_hubble_sa {s : ℝ} (h0 : 0 < s) (h1 : s < π / 2) :
    deriv (hubble sa) s = -(2 / 3) / Real.sin s ^ 2 := by
  have hS := sin_pos_of s h0 h1
  have heq : hubble sa =ᶠ[𝓝 s] fun u => 2 / 3 * (Real.cos u / Real.sin u) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with u hu using sa_hubble u hu.1 hu.2
  rw [heq.deriv_eq]
  have hd := ((Real.hasDerivAt_cos s).div (Real.hasDerivAt_sin s) hS.ne').const_mul (2 / 3 : ℝ)
  have hd' : HasDerivAt (fun u => 2 / 3 * (Real.cos u / Real.sin u))
      (2 / 3 * ((-Real.sin s * Real.sin s - Real.cos s * Real.cos s) / Real.sin s ^ 2)) s := hd
  rw [hd'.deriv]
  have := Real.sin_sq_add_cos_sq s
  field_simp
  linear_combination (-1 : ℝ) * this

theorem sa_cube {s : ℝ} (h0 : 0 < s) (h1 : s < π / 2) : sa s ^ 3 = Real.sin s ^ 2 :=
  cube23 _ (sin_pos_of s h0 h1)

theorem sa_model (Ω t₀ : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hΩ : Ω * Real.cos t₀ ^ 2 = 1) :
    IsFlatLCDM Ω sa t₀ ∧ IsFRCosmo Ω sa (fun R => R + 6 * hubble sa t₀ ^ 2 * (1 - Ω)) t₀ := by
  have hT := sin_pos_of t₀ h0' h1'
  have hCT := cos_pos_of t₀ h0' h1'
  have hs6 : ContDiffAt ℝ 6 sa t₀ :=
    (Real.contDiff_sin.contDiffAt).rpow_const_of_ne hT.ne'
  obtain ⟨hF1, hFk⟩ := iter_affine (6 * hubble sa t₀ ^ 2 * (1 - Ω))
  have hF2 := hFk 0
  have hF3 := hFk 1
  have hF4 := hFk 2
  simp only [zero_add, Nat.reduceAdd] at hF2 hF3 hF4
  have hl0 : 0 < sa t₀ := sa_pos t₀ h0' h1'
  refine ⟨sa_flat Ω t₀ h0' h1' hΩ, ?_⟩
  refine ⟨hl0, sa_H0 t₀ h0' h1', hs6.of_le (by norm_num),
    contDiff_id.add contDiff_const, ?_, ?_, by rw [hF1], by rw [hF4]⟩
  · unfold FriedmannEq rhoM
    simp only [hF1, hF2, div_self hl0.ne', one_pow]
    ring
  · filter_upwards [Ioo_mem_nhds h0' h1'] with t ht
    have hS := sin_pos_of t ht.1 ht.2
    unfold MasterEq rhoM
    simp only [hF1, hF2, hF3]
    rw [deriv_hubble_sa ht.1 ht.2, sa_hubble t₀ h0' h1', div_pow (sa t₀), sa_cube h0' h1',
      sa_cube ht.1 ht.2]
    have hΩ' : Ω = 1 / Real.cos t₀ ^ 2 := by field_simp; linarith
    rw [hΩ']
    field_simp
    ring

theorem eds_model {t₀ : ℝ} (h₀ : 0 < t₀) :
    IsFlatLCDM 1 eds t₀ ∧ IsFRCosmo 1 eds (fun R => R + 6 * hubble eds t₀ ^ 2 * (1 - 1)) t₀ := by
  have hs6 : ContDiffAt ℝ 6 eds t₀ :=
    (contDiff_id.contDiffAt).rpow_const_of_ne h₀.ne'
  obtain ⟨hF1, hFk⟩ := iter_affine (6 * hubble eds t₀ ^ 2 * (1 - 1))
  have hF2 := hFk 0
  have hF3 := hFk 1
  have hF4 := hFk 2
  simp only [zero_add, Nat.reduceAdd] at hF2 hF3 hF4
  have hl0 : 0 < eds t₀ := Real.rpow_pos_of_pos h₀ _
  refine ⟨eds_isFlatLCDM h₀, ?_⟩
  refine ⟨hl0, by rw [hubble_eds h₀]; positivity, hs6.of_le (by norm_num),
    contDiff_id.add contDiff_const, ?_, ?_, by rw [hF1], by rw [hF4]⟩
  · unfold FriedmannEq rhoM
    simp only [hF1, hF2, div_self hl0.ne', one_pow]
    ring
  · filter_upwards [lt_mem_nhds h₀] with t ht
    have hd : deriv (hubble eds) t = -(2 / 3) / t ^ 2 := by
      have heq : hubble eds =ᶠ[𝓝 t] fun u => 2 / 3 / u := by
        filter_upwards [lt_mem_nhds ht] with u hu using hubble_eds hu
      rw [heq.deriv_eq]
      have h2 := (hasDerivAt_inv ht.ne').const_mul (2 / 3 : ℝ)
      have e : (fun u : ℝ => 2 / 3 / u) = fun u => 2 / 3 * u⁻¹ := by funext u; ring
      rw [e, h2.deriv]; field_simp
    unfold MasterEq rhoM
    simp only [hF1, hF2, hF3]
    rw [hd, hubble_eds h₀, div_pow (eds t₀), eds_cube h₀, eds_cube ht]
    field_simp
    ring

/-! ### The upper density bound of `exists_LCDM_model` is redundant -/

theorem exists_LCDM_model_r2 : dropped% Checked.Cosmography.FRCosmo.exists_LCDM_model 2 := by
  intro Ω h0
  rcases lt_trichotomy Ω 1 with h | rfl | h
  · exact exists_LCDM_model h0 h
  · exact ⟨eds, 1, eds_model one_pos⟩
  · obtain ⟨a0, a1, a2⟩ := tO_props Ω h
    exact ⟨sa, tO Ω, sa_model Ω (tO Ω) a0 a1 a2⟩

/-! ### Density zero and below: de Sitter, and the hyperbolic cosine to the power two thirds -/

theorem hubble_exp : hubble Real.exp = fun _ => 1 := by
  funext t; unfold hubble; rw [Real.deriv_exp]; exact div_self (Real.exp_pos t).ne'

theorem exp_model (t₀ : ℝ) :
    IsFlatLCDM 0 Real.exp t₀ ∧
      IsFRCosmo 0 Real.exp (fun R => R + 6 * hubble Real.exp t₀ ^ 2 * (1 - 0)) t₀ := by
  obtain ⟨hF1, hFk⟩ := iter_affine (6 * hubble Real.exp t₀ ^ 2 * (1 - 0))
  have hF2 := hFk 0
  have hF3 := hFk 1
  have hF4 := hFk 2
  simp only [zero_add, Nat.reduceAdd] at hF2 hF3 hF4
  have hl0 : 0 < Real.exp t₀ := Real.exp_pos t₀
  refine ⟨⟨by rw [hubble_exp]; norm_num, ?_⟩, ?_⟩
  · filter_upwards [univ_mem] with t _
    refine ⟨Real.exp_pos t, Real.differentiableAt_exp, ?_⟩
    rw [hubble_exp]; simp
  refine ⟨hl0, by rw [hubble_exp]; norm_num, Real.contDiff_exp.contDiffAt,
    contDiff_id.add contDiff_const, ?_, ?_, by rw [hF1], by rw [hF4]⟩
  · unfold FriedmannEq rhoM
    simp only [hF1, hF2, div_self hl0.ne', one_pow]
    ring
  · filter_upwards [univ_mem] with t _
    have hd : deriv (hubble Real.exp) t = 0 := by rw [hubble_exp]; simp
    unfold MasterEq rhoM
    simp only [hF1, hF2, hF3]
    rw [hd]
    ring

noncomputable def ca (s : ℝ) : ℝ := Real.cosh s ^ (2 / 3 : ℝ)

theorem ca_hasDerivAt (s : ℝ) :
    HasDerivAt ca (Real.sinh s * (2 / 3) * Real.cosh s ^ ((2 / 3 : ℝ) - 1)) s :=
  (Real.hasDerivAt_cosh s).rpow_const (Or.inl (Real.cosh_pos s).ne')

theorem ca_pos (s : ℝ) : 0 < ca s := Real.rpow_pos_of_pos (Real.cosh_pos s) _

theorem ca_hubble (s : ℝ) : hubble ca s = 2 / 3 * (Real.sinh s / Real.cosh s) := by
  have hC := Real.cosh_pos s
  unfold hubble
  rw [(ca_hasDerivAt s).deriv]
  simp only [ca]
  rw [Real.rpow_sub hC, Real.rpow_one]
  have : 0 < Real.cosh s ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hC _
  field_simp

theorem ca_cube (s : ℝ) : ca s ^ 3 = Real.cosh s ^ 2 := cube23 _ (Real.cosh_pos s)

theorem ca_law (Ω t₀ : ℝ) (h0' : 0 < t₀) (hΩ : Ω * Real.sinh t₀ ^ 2 = -1) (s : ℝ) (h0 : 0 < s) :
    hubble ca s = hubble ca t₀ * √(Ω * (1 + redshift ca t₀ s) ^ 3 + 1 - Ω) := by
  have hC := Real.cosh_pos s
  have hCT := Real.cosh_pos t₀
  have hS : 0 < Real.sinh s := Real.sinh_pos_iff.2 h0
  have hST : 0 < Real.sinh t₀ := Real.sinh_pos_iff.2 h0'
  have hz : (1 + redshift ca t₀ s) ^ 3 = Real.cosh t₀ ^ 2 / Real.cosh s ^ 2 := by
    unfold redshift
    rw [show 1 + (ca t₀ / ca s - 1) = ca t₀ / ca s by ring, div_pow, ca_cube, ca_cube]
  rw [hz, ca_hubble s, ca_hubble t₀]
  have e : Ω * (Real.cosh t₀ ^ 2 / Real.cosh s ^ 2) + 1 - Ω
      = (Real.cosh t₀ / Real.sinh t₀ * (Real.sinh s / Real.cosh s)) ^ 2 := by
    have hΩ' : Ω = -1 / Real.sinh t₀ ^ 2 := by field_simp; linarith
    rw [hΩ']
    have := Real.cosh_sq s
    have := Real.cosh_sq t₀
    field_simp
    nlinarith
  rw [e, Real.sqrt_sq (by positivity)]
  field_simp

theorem deriv_hubble_ca (s : ℝ) : deriv (hubble ca) s = 2 / 3 / Real.cosh s ^ 2 := by
  have hC := Real.cosh_pos s
  have heq : hubble ca = fun u => 2 / 3 * (Real.sinh u / Real.cosh u) := by
    funext u; exact ca_hubble u
  rw [heq]
  have hd := ((Real.hasDerivAt_sinh s).div (Real.hasDerivAt_cosh s) hC.ne').const_mul (2 / 3 : ℝ)
  have hd' : HasDerivAt (fun u => 2 / 3 * (Real.sinh u / Real.cosh u))
      (2 / 3 * ((Real.cosh s * Real.cosh s - Real.sinh s * Real.sinh s) / Real.cosh s ^ 2)) s := hd
  rw [hd'.deriv]
  have := Real.cosh_sq s
  field_simp
  linear_combination this

theorem ca_model (Ω t₀ : ℝ) (h0' : 0 < t₀) (hΩ : Ω * Real.sinh t₀ ^ 2 = -1) :
    IsFlatLCDM Ω ca t₀ ∧ IsFRCosmo Ω ca (fun R => R + 6 * hubble ca t₀ ^ 2 * (1 - Ω)) t₀ := by
  have hCT := Real.cosh_pos t₀
  have hST : 0 < Real.sinh t₀ := Real.sinh_pos_iff.2 h0'
  have hs6 : ContDiffAt ℝ 6 ca t₀ :=
    (Real.contDiff_cosh.contDiffAt).rpow_const_of_ne hCT.ne'
  obtain ⟨hF1, hFk⟩ := iter_affine (6 * hubble ca t₀ ^ 2 * (1 - Ω))
  have hF2 := hFk 0
  have hF3 := hFk 1
  have hF4 := hFk 2
  simp only [zero_add, Nat.reduceAdd] at hF2 hF3 hF4
  have hl0 : 0 < ca t₀ := ca_pos t₀
  have hH0 : 0 < hubble ca t₀ := by rw [ca_hubble]; positivity
  refine ⟨⟨hH0, ?_⟩, ?_⟩
  · filter_upwards [lt_mem_nhds h0'] with s hs
    exact ⟨ca_pos s, (ca_hasDerivAt s).differentiableAt, ca_law Ω t₀ h0' hΩ s hs⟩
  refine ⟨hl0, hH0, hs6.of_le (by norm_num),
    contDiff_id.add contDiff_const, ?_, ?_, by rw [hF1], by rw [hF4]⟩
  · unfold FriedmannEq rhoM
    simp only [hF1, hF2, div_self hl0.ne', one_pow]
    ring
  · filter_upwards [univ_mem] with t _
    have hC := Real.cosh_pos t
    unfold MasterEq rhoM
    simp only [hF1, hF2, hF3]
    rw [deriv_hubble_ca, ca_hubble t₀, div_pow (ca t₀), ca_cube, ca_cube]
    have hΩ' : Ω = -1 / Real.sinh t₀ ^ 2 := by field_simp; linarith
    rw [hΩ']
    field_simp
    ring

/-! ### The lower density bound of `exists_LCDM_model` is redundant -/

theorem exists_LCDM_model_r1 : dropped% Checked.Cosmography.FRCosmo.exists_LCDM_model 1 := by
  intro Ω h1
  rcases lt_trichotomy Ω 0 with h | rfl | h
  · set t₀ := Real.arsinh (1 / √(-Ω))
    have hq : 0 < √(-Ω) := Real.sqrt_pos.2 (by linarith)
    have h0' : 0 < t₀ := Real.arsinh_pos_iff.2 (by positivity)
    have hΩ : Ω * Real.sinh t₀ ^ 2 = -1 := by
      rw [Real.sinh_arsinh, div_pow, Real.sq_sqrt (by linarith)]
      field_simp
      rw [div_self h.ne]
    exact ⟨ca, t₀, ca_model Ω t₀ h0' hΩ⟩
  · exact ⟨Real.exp, 0, exp_model 0⟩
  · exact exists_LCDM_model h h1

/-! ### The lower density bound of the two refutations at a density is redundant -/

theorem model_nonpos {Ω : ℝ} (h : Ω ≤ 0) : ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ ∧
    ContDiffAt ℝ 6 a t₀ ∧ IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ := by
  rcases lt_or_eq_of_le h with h | rfl
  · set t₀ := Real.arsinh (1 / √(-Ω))
    have hq : 0 < √(-Ω) := Real.sqrt_pos.2 (by linarith)
    have h0' : 0 < t₀ := Real.arsinh_pos_iff.2 (by positivity)
    have hΩ : Ω * Real.sinh t₀ ^ 2 = -1 := by
      rw [Real.sinh_arsinh, div_pow, Real.sq_sqrt (by linarith)]
      field_simp
      rw [div_self h.ne]
    obtain ⟨hL, hM⟩ := ca_model Ω t₀ h0' hΩ
    exact ⟨ca, t₀, hL, (Real.contDiff_cosh.contDiffAt).rpow_const_of_ne (Real.cosh_pos t₀).ne', hM⟩
  · obtain ⟨hL, hM⟩ := exp_model 0
    exact ⟨Real.exp, 0, hL, Real.contDiff_exp.contDiffAt, hM⟩

theorem facts_nonpos {Ω : ℝ} (h : Ω ≤ 0) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ ∧
      decel a t₀ = 3 / 2 * Ω - 1 ∧ cosmoCoeff 3 a t₀ = 1 ∧ cosmoCoeff 4 a t₀ = 1 - 9 / 2 * Ω ∧
      cosmoCoeff 5 a t₀ = 1 + 3 * Ω + 27 / 2 * Ω ^ 2 ∧
      curv a t₀ = -6 * hubble a t₀ ^ 2 * (1 - (3 / 2 * Ω - 1)) := by
  obtain ⟨a, t₀, hL, h6, hM⟩ := model_nonpos h
  obtain ⟨hq, hj, hs, hl, -⟩ := flatLCDM_coeffs Ω a t₀ hL h6
  obtain ⟨hR0, -, -, -⟩ := curv_derivs a t₀ hM.pos hM.expanding hM.smooth_a
  exact ⟨a, t₀, hM, hq, hj, hs, hl, by rw [hR0, hq]⟩

theorem printedF0Mul_false_at_r1 :
    dropped% Checked.Cosmography.FRCosmo.printedF0Mul_false_at 1 := by
  intro Ω h1
  rcases lt_or_ge 0 Ω with h0 | h0
  · exact printedF0Mul_false_at h0 h1
  intro h
  obtain ⟨a, t₀, hM, hq, hj, hs, hl, hR0⟩ := facts_nonpos h0
  have e := h a _ t₀ hM
  rw [hq, hj, hs, hl, hR0] at e
  simp only [printedR, P0, Q0] at e
  have hH := hM.expanding
  have k : hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) = 0 := by
    linear_combination (-2 / 3 : ℝ) * e
  have : 0 < hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) := by
    have := quad_pos Ω
    have : 0 < 2 - Ω := by linarith
    positivity
  linarith

theorem printedF0_false_at_r1 :
    dropped% Checked.Cosmography.FRCosmo.printedF0_false_at 1 := by
  intro Ω h1 hR
  rcases lt_or_ge 0 Ω with h0 | h0
  · exact printedF0_false_at h0 h1 hR
  intro h
  obtain ⟨a, t₀, hM, hq, hj, hs, hl, hR0⟩ := facts_nonpos h0
  have hne : printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 := by
    rw [hq, hj, hs, hl]
    simp only [printedR]
    intro e
    apply hR
    linear_combination (-16 : ℝ) * e
  have e := h a _ t₀ hM hne
  have hH := hM.expanding
  rw [div_eq_div_iff (by positivity) hne] at e
  rw [hq, hj, hs, hl, hR0] at e
  simp only [printedR, P0, Q0] at e
  have k : hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) = 0 := by
    linear_combination (-2 / 3 : ℝ) * e
  have : 0 < hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) := by
    have := quad_pos Ω
    have : 0 < 2 - Ω := by linarith
    positivity
  linarith

end Checked.Trust.NecessityAW
