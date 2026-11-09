import Checked.Cosmography.BambaZ
import Checked.Cosmography.Transverse
import Checked.Cosmography.FRCosmo
import Checked.Cosmography.CPLCoefficients
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Certified phrase lines (trust track part 3, run 2026-11-09T1828Z)

The plain-words phrase of a pinned definition in a generated claim (`CLAIMS.md`) is a sequence of
lines written by blind readers (`scripts/trust/phrase_roles.txt`). Until this run no check read what
those lines say about the definition: a line was shown because a reader wrote it and the main session
judged it true of the Lean body. Each theorem below proves, about the Lean definition itself, the
property one registered reader line states (`scripts/trust/phrase_certs.txt` names the line and the
theorem; rule P13 of `scripts/trust/check_claims.py`). Where the property needs conditions the line
does not state, the theorem carries them as hypotheses and `scripts/trust/Claims.lean` prints them next
to the phrase in every generated claim that uses the definition: a reader sees exactly what was proved.

Several lines turned out to hold only under such conditions (Mathlib's total arithmetic: `x / 0 = 0`):
"positive curvature constant gives above one" (Ω0) needs a nonzero Hubble rate and scale factor,
"zero when emission and observation coincide" (redshift) a nonzero scale factor, "orders 0 and 1
coefficients are one" (cosmographic coefficients) a nonzero scale factor and, for order 1, a nonzero
velocity. The theorems `*_needs_*` show these conditions cannot be dropped.
-/

open Filter Topology Checked.Cosmography Checked.Cosmography.Aviles

namespace Checked.Trust.PhraseCerts

/-! ### Hubble rate, deceleration parameter, redshift -/

/-- Line "positive for expansion and negative for contraction" of `hubble`. -/
theorem hubble_sign (a : ℝ → ℝ) (t : ℝ) (ha : 0 < a t) :
    (0 < deriv a t → 0 < hubble a t) ∧ (deriv a t < 0 → hubble a t < 0) := by
  unfold hubble
  exact ⟨fun h => div_pos h ha, fun h => div_neg_of_neg_of_pos h ha⟩

/-- Line "logarithmic derivative of the scale factor with respect to cosmic time" of `hubble`: for a
positive scale factor differentiable at `t`. -/
theorem hubble_log_deriv (a : ℝ → ℝ) (t : ℝ) (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) :
    HasDerivAt (fun s => Real.log (a s)) (hubble a t) t := by
  unfold hubble
  exact hd.hasDerivAt.log ha.ne'

/-- Line "one plus redshift is the scale factor at observation over that at emission" of `redshift`. -/
theorem one_add_redshift (a : ℝ → ℝ) (t₀ t : ℝ) : 1 + redshift a t₀ t = a t₀ / a t := by
  unfold redshift; ring

/-- Line "The order 2 coefficient is minus the deceleration parameter usually written q" of
`cosmoCoeff`, for a nonzero scale factor. -/
theorem cosmoCoeff_two (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0) : cosmoCoeff 2 a t = -decel a t := by
  unfold cosmoCoeff decel hubble
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  by_cases hv : deriv a t = 0
  · simp [hv]
  · field_simp

/-- Line "negative value means accelerating expansion" of `decel`. -/
theorem decel_neg_iff (a : ℝ → ℝ) (t : ℝ) (ha : 0 < a t) (hv : deriv a t ≠ 0) :
    decel a t < 0 ↔ 0 < deriv (deriv a) t := by
  unfold decel
  have hv2 : 0 < deriv a t ^ 2 := by positivity
  rw [div_lt_iff₀ hv2, zero_mul, neg_lt_zero]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith
  · intro h
    exact mul_pos h ha

/-- Sign line "positive when emission precedes observation in an expanding universe" of `redshift`. -/
theorem redshift_pos (a : ℝ → ℝ) (t₀ t : ℝ) (hpos : ∀ s, 0 < a s) (hexp : StrictMono a) (ht : t < t₀) :
    0 < redshift a t₀ t := by
  unfold redshift
  have h1 : 1 < a t₀ / a t := (one_lt_div (hpos t)).mpr (hexp ht)
  linarith

/-- Line "zero when emission and observation coincide" of `redshift`. -/
theorem redshift_self (a : ℝ → ℝ) (t₀ : ℝ) (ha : a t₀ ≠ 0) : redshift a t₀ t₀ = 0 := by
  unfold redshift
  rw [div_self ha]; ring

/-- The condition of `redshift_self` is needed: for the zero scale factor the redshift at
coinciding times is `-1` (Mathlib: `0 / 0 = 0`). -/
theorem redshift_self_needs_ne : redshift (fun _ => 0) 0 0 = -1 := by
  unfold redshift; simp

/-- Line "orders 0 and 1 coefficients are one" of `cosmoCoeff`. -/
theorem cosmoCoeff_zero_one (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0) (hv : deriv a t ≠ 0) :
    cosmoCoeff 0 a t = 1 ∧ cosmoCoeff 1 a t = 1 := by
  unfold cosmoCoeff hubble
  refine ⟨by simp [ha], ?_⟩
  simp only [iteratedDeriv_one, pow_one]
  field_simp

/-- The conditions of `cosmoCoeff_zero_one` are needed: a scale factor with zero velocity has
order-1 coefficient `0`. -/
theorem cosmoCoeff_one_needs_velocity : cosmoCoeff 1 (fun _ => 1) 0 = 0 := by
  unfold cosmoCoeff hubble; simp

/-! ### Curvature quantities (Bamba et al.) -/

/-- Line "one plus curvature term" (first part of the sign line) of `omega0`, and line "total
density parameter minus one" of `curvK`: unconditional. -/
theorem omega0_eq_one_add_curvK (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    BambaK.omega0 K a t₀ = 1 + BambaZ.curvK K a t₀ := by
  unfold BambaK.omega0 BambaZ.curvK; rfl

/-- Line "total density parameter minus one" of `curvK`. -/
theorem curvK_eq_omega0_sub_one (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    BambaZ.curvK K a t₀ = BambaK.omega0 K a t₀ - 1 := by
  rw [omega0_eq_one_add_curvK]; ring

/-- Sign line "positive curvature constant gives above one" of `omega0`: only for a nonzero
Hubble rate and scale factor at `t₀`. -/
theorem omega0_gt_one (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hK : 0 < K) (hH : hubble a t₀ ≠ 0)
    (ha : a t₀ ≠ 0) : 1 < BambaK.omega0 K a t₀ := by
  unfold BambaK.omega0
  have : 0 < K / (hubble a t₀ ^ 2 * a t₀ ^ 2) := by positivity
  linarith

/-- The condition of `omega0_gt_one` is needed: with zero velocity at `t₀` (Hubble rate zero)
`omega0` is exactly one for every curvature constant. -/
theorem omega0_needs_hubble (K : ℝ) : BambaK.omega0 K (fun _ => 1) 0 = 1 := by
  unfold BambaK.omega0 hubble; simp

/-- Line "equals one for zero curvature" of `omega0`. -/
theorem omega0_zero (a : ℝ → ℝ) (t₀ : ℝ) : BambaK.omega0 0 a t₀ = 1 := by
  unfold BambaK.omega0; simp

/-- Line "positive for closed and negative for open" and sign line "has sign of curvature
constant" of `curvK`: only for a nonzero Hubble rate and scale factor at `t₀`. -/
theorem curvK_sign (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hH : hubble a t₀ ≠ 0) (ha : a t₀ ≠ 0) :
    (0 < K → 0 < BambaZ.curvK K a t₀) ∧ (K < 0 → BambaZ.curvK K a t₀ < 0) := by
  unfold BambaZ.curvK
  have hd : 0 < hubble a t₀ ^ 2 * a t₀ ^ 2 := by positivity
  exact ⟨fun h => div_pos h hd, fun h => div_neg_of_neg_of_pos h hd⟩

/-- Line "always below one for a positive scale factor" of `yred`. -/
theorem yred_lt_one (a : ℝ → ℝ) (t₀ t : ℝ) (ha : 0 < a t) (ha₀ : 0 < a t₀) :
    BambaY.yred a t₀ t < 1 := by
  unfold BambaY.yred redshift
  have h1 : 1 + (a t₀ / a t - 1) = a t₀ / a t := by ring
  rw [h1, div_lt_one (div_pos ha₀ ha)]
  linarith

/-- Line "one minus the scale factor at emission over that at observation" of `yred`, for nonzero
scale factors at both times. -/
theorem yred_eq (a : ℝ → ℝ) (t₀ t : ℝ) (ha : a t ≠ 0) (ha₀ : a t₀ ≠ 0) :
    BambaY.yred a t₀ t = 1 - a t / a t₀ := by
  unfold BambaY.yred redshift
  have h : 1 + (a t₀ / a t - 1) = a t₀ / a t := by ring
  rw [h]
  field_simp

/-- Sign line "positive for redshift, negative for blueshift" of `yred`, for a positive scale factor. -/
theorem yred_sign (a : ℝ → ℝ) (t₀ t : ℝ) (ha : 0 < a t) (ha₀ : 0 < a t₀) :
    (0 < redshift a t₀ t → 0 < BambaY.yred a t₀ t) ∧ (redshift a t₀ t < 0 → BambaY.yred a t₀ t < 0) := by
  have hp : 0 < 1 + redshift a t₀ t := by
    unfold redshift
    have := div_pos ha₀ ha
    linarith
  unfold BambaY.yred
  exact ⟨fun h => div_pos h hp, fun h => div_neg_of_neg_of_pos h hp⟩

/-! ### Transverse comoving function -/

/-- Line "equals χ itself for zero K" of `transverse`. -/
theorem transverse_zero (χ : ℝ) : Transverse.transverse 0 χ = χ := by
  unfold Transverse.transverse; simp

/-- Sign line "positive curvature constant gives sine" of `transverse`. -/
theorem transverse_pos (K χ : ℝ) (hK : 0 < K) :
    Transverse.transverse K χ = Real.sin (Real.sqrt K * χ) / Real.sqrt K := by
  unfold Transverse.transverse; simp [hK]

/-- Line "vanishes at zero with unit slope" of `transverse`, for every curvature constant. -/
theorem transverse_origin (K : ℝ) :
    Transverse.transverse K 0 = 0 ∧ HasDerivAt (Transverse.transverse K) 1 0 := by
  refine ⟨by unfold Transverse.transverse; split_ifs <;> simp, ?_⟩
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · have hs : 0 < Real.sqrt (-K) := Real.sqrt_pos.mpr (by linarith)
    have hf : Transverse.transverse K = fun χ => Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K) := by
      funext χ; unfold Transverse.transverse; simp [hK, not_lt.mpr hK.le]
    rw [hf]
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (Real.sqrt (-K))).sinh).div_const (Real.sqrt (-K))
    convert this using 1
    · rfl
    · rw [id_eq, mul_zero, Real.cosh_zero, one_mul, mul_one, div_self hs.ne']
  · have hf : Transverse.transverse 0 = fun χ => χ := by funext χ; exact transverse_zero χ
    rw [hf]; exact hasDerivAt_id 0
  · have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
    have hf : Transverse.transverse K = fun χ => Real.sin (Real.sqrt K * χ) / Real.sqrt K := by
      funext χ; exact transverse_pos K χ hK
    rw [hf]
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (Real.sqrt K)).sin).div_const (Real.sqrt K)
    convert this using 1
    · rfl
    · rw [id_eq, mul_zero, Real.cos_zero, one_mul, mul_one, div_self hs.ne']

/-! ### f(R) cosmology: Ricci scalar and dust density -/

/-- Lines "negative convention so de Sitter has minus twelve times Hubble rate squared" and sign line
"de Sitter has negative Ricci scalar" of `curv`: for the de Sitter scale factor `c e^{Ht}`, `c ≠ 0`,
the Ricci scalar is `-12 H²`, negative when `H ≠ 0`. -/
theorem curv_deSitter (c H t : ℝ) (hc : c ≠ 0) :
    FRCosmo.curv (fun s => c * Real.exp (H * s)) t = -12 * H ^ 2 ∧
      (H ≠ 0 → FRCosmo.curv (fun s => c * Real.exp (H * s)) t < 0) := by
  have hhub : hubble (fun s => c * Real.exp (H * s)) = fun _ => H := by
    funext s
    unfold hubble
    have hd : HasDerivAt (fun s => c * Real.exp (H * s)) (c * (Real.exp (H * s) * H)) s :=
      (((hasDerivAt_id s).const_mul H).exp.congr_deriv (by simp)).const_mul c
    rw [hd.deriv]
    have := Real.exp_pos (H * s)
    field_simp
  have hcurv : FRCosmo.curv (fun s => c * Real.exp (H * s)) t = -12 * H ^ 2 := by
    unfold FRCosmo.curv
    rw [hhub]
    simp only [deriv_const']
    ring
  refine ⟨hcurv, fun hH => ?_⟩
  rw [hcurv]
  have : 0 < H ^ 2 := by positivity
  linarith

/-- Line "falls as the inverse cube of the scale factor" of `rhoM`: `ρ_M · a³` is the same at every
time where the scale factor is nonzero. -/
theorem rhoM_cube (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (ha : a t ≠ 0) :
    FRCosmo.rhoM Ω a t₀ t * a t ^ 3 = 3 * hubble a t₀ ^ 2 * Ω * a t₀ ^ 3 := by
  unfold FRCosmo.rhoM
  field_simp

/-! ### Expansion laws -/

/-- Line "present Hubble rate is positive so the universe is expanding" of `IsFlatLCDM`. -/
theorem flatLCDM_expanding (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (h : IsFlatLCDM Ω a t₀) :
    0 < hubble a t₀ ∧ 0 < deriv a t₀ := by
  refine ⟨h.1, ?_⟩
  have ha : 0 < a t₀ := h.2.self_of_nhds.1
  have := h.1
  unfold hubble at this
  exact (div_pos_iff_of_pos_right ha).mp this

/-- Line "present Hubble rate is positive so the universe is expanding" of `IsFlatCPL`. -/
theorem flatCPL_expanding (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (h : CPL.IsFlatCPL Ω w₀ wₐ a t₀) :
    0 < hubble a t₀ ∧ 0 < deriv a t₀ := by
  refine ⟨h.1, ?_⟩
  have ha : 0 < a t₀ := h.2.self_of_nhds.1
  have := h.1
  unfold hubble at this
  exact (div_pos_iff_of_pos_right ha).mp this

/-! ### Chemistry -/

/-- Line "first and second volume derivatives of pressure both vanish" of `IsCriticalIsotherm`. -/
theorem critical_iff (p : ℝ → ℝ) (v : ℝ) :
    Chemistry.CubicEOS.IsCriticalIsotherm p v ↔ deriv p v = 0 ∧ deriv (deriv p) v = 0 := Iff.rfl

/-- Line "a mere stationary point is not critical" of `IsCriticalIsotherm`: `v ↦ v²` is stationary
at `0` and not critical there. -/
theorem stationary_not_critical :
    deriv (fun v : ℝ => v ^ 2) 0 = 0 ∧ ¬ Chemistry.CubicEOS.IsCriticalIsotherm (fun v : ℝ => v ^ 2) 0 := by
  have h1 : deriv (fun v : ℝ => v ^ 2) = fun v => 2 * v := by
    funext v; simp
  refine ⟨by rw [h1]; simp, fun h => ?_⟩
  have h2 := h.2
  rw [h1] at h2
  have : deriv (fun v : ℝ => 2 * v) 0 = 2 := by
    rw [deriv_const_mul _ differentiableAt_id]; simp
  rw [this] at h2
  norm_num at h2

/-- Lines "liquid volume is less than gas volume", "pressure equals the saturation pressure at both
volumes" and "equal areas between the isotherm and the saturation pressure line" of
`IsMaxwellCoexistence`. -/
theorem maxwell_parts (p : ℝ → ℝ) (vl vg ps : ℝ) (h : Chemistry.Coexistence.IsMaxwellCoexistence p vl vg ps) :
    vl < vg ∧ (p vl = ps ∧ p vg = ps) ∧ ∫ v in vl..vg, p v = ps * (vg - vl) :=
  ⟨h.1, ⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩

end Checked.Trust.PhraseCerts
