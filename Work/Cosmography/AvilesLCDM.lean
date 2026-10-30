import Mathlib
import Checked.Cosmography.Lookback

/-!
# Candidate C2: Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007, Eq. (15)

Source (typeset text verified in run 2026-10-30T0220Z by rendering p. 10 of arXiv v2):
"To evaluate the CS for ΛCDM we use Eqs. (4) with H = H₀ √(Ω_m (1+z)³ + 1 − Ω_m), yielding
 q₀ = −1 + 3/2 Ω_m, j₀ = 1, s₀ = 1 − 9/2 Ω_m, l₀ = 1 + 3Ω_m − 27/2 Ω_m²,
 m₀ = 1 − 27/2 Ω_m² − 81 Ω_m² − 81/2 Ω_m³."
Definitions (their Eq. (3)): q = −ä/(aH²), j = a⁽³⁾/(aH³), s = a⁽⁴⁾/(aH⁴), l = a⁽⁵⁾/(aH⁵),
m = a⁽⁶⁾/(aH⁶), evaluated at t₀.

Conventions: `cosmoCoeff n a t = a⁽ⁿ⁾(t) / (a(t) H(t)ⁿ)`, so j = cosmoCoeff 3, s = 4, l = 5,
m = 6. `IsFlatLCDM Ω a t₀`: near t₀, a > 0, a differentiable, and H(t) = H₀ √(Ω(1+z)³ + 1 − Ω)
with z the redshift relative to t₀, and H₀ > 0 (expanding). This is the paper's model sentence,
nothing more; in particular no value of Ω is excluded.

Draft: frozen claim + refutation on Einstein–de Sitter (Ω = 1, a = t^{2/3}).
-/

namespace Work.Cosmography.Aviles

open Filter Topology Checked.Cosmography

/-- `n`-th cosmographic coefficient `a⁽ⁿ⁾ / (a Hⁿ)` (Aviles et al. Eq. (3): j, s, l, m for
`n = 3, 4, 5, 6`; q is `-cosmoCoeff 2`). -/
noncomputable def cosmoCoeff (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  iteratedDeriv n a t / (a t * hubble a t ^ n)

/-- Flat ΛCDM with matter fraction `Ω` at observation time `t₀` (Aviles et al., text before
Eq. (15)): `H = H₀ √(Ω(1+z)³ + 1 − Ω)` near `t₀`, with `H₀ > 0`. -/
def IsFlatLCDM (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)

/-- The printed claim for `l₀` (frozen verbatim from Eq. (15)). -/
def AvilesL0Claim : Prop :=
  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
    cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2

/-- The printed claim for `m₀` (frozen verbatim from Eq. (15)). -/
def AvilesM0Claim : Prop :=
  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
    cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3

/-! ## Einstein–de Sitter: `a(t) = t^{2/3}` -/

noncomputable def eds : ℝ → ℝ := fun t => t ^ (2 / 3 : ℝ)

lemma iter_eds (k : ℕ) (t : ℝ) :
    deriv^[k] eds t = (descPochhammer ℝ k).eval (2 / 3 : ℝ) * t ^ ((2 / 3 : ℝ) - k) :=
  Real.iter_deriv_rpow_const _ _ _

lemma deriv_eds (t : ℝ) : deriv eds t = 2 / 3 * t ^ ((2 / 3 : ℝ) - 1) := by
  have := iter_eds 1 t
  simpa using this

lemma hubble_eds {t : ℝ} (ht : 0 < t) : hubble eds t = 2 / 3 / t := by
  unfold hubble
  rw [deriv_eds, eds, Real.rpow_sub ht, Real.rpow_one]
  have : 0 < t ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos ht _
  field_simp

lemma eds_cube {t : ℝ} (ht : 0 < t) : (eds t) ^ 3 = t ^ 2 := by
  unfold eds
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

/-- Einstein–de Sitter is flat ΛCDM with `Ω = 1`. -/
theorem eds_isFlatLCDM {t₀ : ℝ} (h₀ : 0 < t₀) : IsFlatLCDM 1 eds t₀ := by
  refine ⟨by rw [hubble_eds h₀]; positivity, ?_⟩
  filter_upwards [lt_mem_nhds h₀] with t ht
  refine ⟨Real.rpow_pos_of_pos ht _, ?_, ?_⟩
  · exact (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).differentiableAt
  · rw [hubble_eds ht, hubble_eds h₀, redshift]
    have e0 : 0 < eds t₀ := Real.rpow_pos_of_pos h₀ _
    have e1 : 0 < eds t := Real.rpow_pos_of_pos ht _
    have : (1 : ℝ) * (1 + (eds t₀ / eds t - 1)) ^ 3 + 1 - 1 = (t₀ / t) ^ 2 := by
      rw [div_pow, ← eds_cube h₀, ← eds_cube ht]; field_simp; try ring
    rw [this, Real.sqrt_sq (by positivity)]
    field_simp

lemma cosmoCoeff_eds (n : ℕ) {t : ℝ} (ht : 0 < t) :
    cosmoCoeff n eds t = (descPochhammer ℝ n).eval (2 / 3 : ℝ) / (2 / 3) ^ n := by
  unfold cosmoCoeff
  rw [iteratedDeriv_eq_iterate, iter_eds, hubble_eds ht, eds, Real.rpow_sub ht,
    Real.rpow_natCast]
  have : 0 < t ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos ht _
  have h2 : (2 / (3 * t)) ^ n * t ^ n = (2 / 3) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  field_simp
  linear_combination (-(Polynomial.eval (2 / 3 : ℝ) (descPochhammer ℝ n))) * h2

theorem l0_eds {t : ℝ} (ht : 0 < t) : cosmoCoeff 5 eds t = 35 / 2 := by
  rw [cosmoCoeff_eds 5 ht]
  simp [descPochhammer_succ_right]
  norm_num

theorem m0_eds {t : ℝ} (ht : 0 < t) : cosmoCoeff 6 eds t = -455 / 4 := by
  rw [cosmoCoeff_eds 6 ht]
  simp [descPochhammer_succ_right]
  norm_num

/-- **Refutation of the printed l₀ in Eq. (15).** On Einstein–de Sitter (Ω = 1) the printed
formula gives `−19/2`, the true value is `35/2`. -/
theorem avilesL0Claim_false : ¬ AvilesL0Claim := by
  intro h
  have := h 1 eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)
  rw [l0_eds one_pos] at this
  norm_num at this

/-- **Refutation of the printed m₀ in Eq. (15).** On Einstein–de Sitter the printed formula
gives `−134`, the true value is `−455/4`. -/
theorem avilesM0Claim_false : ¬ AvilesM0Claim := by
  intro h
  have := h 1 eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)
  rw [m0_eds one_pos] at this
  norm_num at this


/-- If `F` vanishes near `x` and has derivative `G` near `x`, then `G` vanishes near `x`. -/
lemma step {F G : ℝ → ℝ} {x : ℝ} (hF : ∀ᶠ t in 𝓝 x, F t = 0)
    (hG : ∀ᶠ t in 𝓝 x, HasDerivAt F (G t) t) : ∀ᶠ t in 𝓝 x, G t = 0 := by
  filter_upwards [hF.eventually_nhds, hG] with t hFt hGt
  have h : F =ᶠ[𝓝 t] fun _ => (0 : ℝ) := hFt
  rw [← hGt.deriv, h.deriv_eq]
  simp

/-- **Cosmographic coefficients of flat ΛCDM** (correct version of Aviles et al. Eq. (15)).
For any scale factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` near `t₀` and six times continuously
differentiable at `t₀`: `q₀ = 3Ω/2 − 1`, `j₀ = 1`, `s₀ = 1 − 9Ω/2`, `l₀ = 1 + 3Ω + 27Ω²/2`,
`m₀ = 1 − 27Ω/2 − 81Ω² − 81Ω³/4`. -/
theorem flatLCDM_coeffs (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM Ω a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) :
    decel a t₀ = 3 / 2 * Ω - 1 ∧ cosmoCoeff 3 a t₀ = 1 ∧ cosmoCoeff 4 a t₀ = 1 - 9 / 2 * Ω ∧
    cosmoCoeff 5 a t₀ = 1 + 3 * Ω + 27 / 2 * Ω ^ 2 ∧
    cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω - 81 * Ω ^ 2 - 81 / 4 * Ω ^ 3 := by
  obtain ⟨hH, hev⟩ := hL
  set D : ℕ → ℝ → ℝ := fun k => deriv^[k] a with hD
  set a₀ := a t₀ with ha₀
  set H₀ := hubble a t₀ with hH₀
  have ha0 : 0 < a₀ := hev.self_of_nhds.1
  have hsm : ∀ᶠ t in 𝓝 t₀, ContDiffAt ℝ 6 a t := hs.eventually (by simp)
  have key : ∀ k t, DifferentiableAt ℝ (D k) t → HasDerivAt (D k) (D (k+1) t) t := by
    intro k t hk
    have := hk.hasDerivAt
    simpa [hD, Function.iterate_succ_apply'] using this
  have cds : ∀ t, ContDiffAt ℝ 6 a t →
      ContDiffAt ℝ 5 (D 1) t ∧ ContDiffAt ℝ 4 (D 2) t ∧ ContDiffAt ℝ 3 (D 3) t ∧
      ContDiffAt ℝ 2 (D 4) t ∧ ContDiffAt ℝ 1 (D 5) t := by
    intro t h
    have c5 : ContDiffAt ℝ 5 (D 1) t := h.derivWithin (by norm_num)
    have c4 : ContDiffAt ℝ 4 (D 2) t := c5.derivWithin (by norm_num)
    have c3 : ContDiffAt ℝ 3 (D 3) t := c4.derivWithin (by norm_num)
    have c2 : ContDiffAt ℝ 2 (D 4) t := c3.derivWithin (by norm_num)
    have c1 : ContDiffAt ℝ 1 (D 5) t := c2.derivWithin (by norm_num)
    exact ⟨c5, c4, c3, c2, c1⟩
  have hder : ∀ᶠ t in 𝓝 t₀, HasDerivAt (D 0) (D 1 t) t ∧ HasDerivAt (D 1) (D 2 t) t ∧
      HasDerivAt (D 2) (D 3 t) t ∧ HasDerivAt (D 3) (D 4 t) t ∧ HasDerivAt (D 4) (D 5 t) t ∧
      HasDerivAt (D 5) (D 6 t) t := by
    filter_upwards [hsm] with t h
    obtain ⟨c5, c4, c3, c2, c1⟩ := cds t h
    exact ⟨key 0 t (h.differentiableAt (by norm_num)), key 1 t (c5.differentiableAt (by norm_num)),
      key 2 t (c4.differentiableAt (by norm_num)), key 3 t (c3.differentiableAt (by norm_num)),
      key 4 t (c2.differentiableAt (by norm_num)), key 5 t (c1.differentiableAt (by norm_num))⟩
  have he0 : D 0 t₀ = a₀ := rfl
  have he1 : D 1 t₀ = H₀ * a₀ := by
    have h1 : D 1 t₀ = deriv a t₀ := rfl
    rw [h1, hH₀, hubble, ← ha₀]
    field_simp
  -- the squared Hubble law, polynomial form
  have harg : ∀ᶠ t in 𝓝 t₀, 0 < Ω * (a₀ / a t) ^ 3 + 1 - Ω := by
    have hc : ContinuousAt (fun t => Ω * (a₀ / a t) ^ 3 + 1 - Ω) t₀ := by
      have : ContinuousAt a t₀ := hs.continuousAt
      fun_prop (disch := exact ha0.ne')
    have h1 : (0 : ℝ) < Ω * (a₀ / a t₀) ^ 3 + 1 - Ω := by
      rw [← ha₀, div_self ha0.ne']; norm_num
    exact hc.eventually (lt_mem_nhds h1)
  have hE : ∀ᶠ t in 𝓝 t₀, (((H₀^2*(Ω - 1)) * (D 0 t ^ 3)) + ((1) * (D 0 t * D 1 t ^ 2))) + ((-a₀^3*H₀^2*Ω)) = 0 := by
    filter_upwards [hev, harg] with t ⟨hat, _, hHt⟩ hpos
    rw [redshift, add_sub_cancel, ← ha₀] at hHt
    have hsq := congrArg (fun x => x ^ 2) hHt
    simp only [hubble, mul_pow, Real.sq_sqrt hpos.le] at hsq
    have hsq' : deriv a t ^ 2 = a t ^ 2 * (H₀ ^ 2 * (Ω * (a₀ ^ 3 / a t ^ 3) + 1 - Ω)) := by
      rw [div_pow, div_eq_iff (pow_pos hat 2).ne'] at hsq
      rw [hsq, div_pow]; ring
    have hid : a t * (a t ^ 2 * (H₀ ^ 2 * (Ω * (a₀ ^ 3 / a t ^ 3) + 1 - Ω))) =
        H₀ ^ 2 * Ω * a₀ ^ 3 + H₀ ^ 2 * (1 - Ω) * a t ^ 3 := by
      field_simp; try ring
    simp only [hD, Function.iterate_zero, Function.iterate_one, id]
    linear_combination (a t) * hsq' + hid
  have dE : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((H₀^2*(Ω - 1)) * (D 0 t ^ 3)) + ((1) * (D 0 t * D 1 t ^ 2))) + ((-a₀^3*H₀^2*Ω))) (D 1 t * ((((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2)) + ((2) * (D 0 t * D 2 t))) + ((1) * (D 1 t ^ 2)))) t := by
    filter_upwards [hder] with t ⟨h0, h1, h2, h3, h4, h5⟩
    exact (((((h0.pow 3).const_mul (H₀^2*(Ω - 1))).add ((h0.mul (h1.pow 2)).const_mul (1))).add (hasDerivAt_const t (-a₀^3*H₀^2*Ω)))).congr_deriv (by (try simp only [Pi.pow_apply]); push_cast; ring)
  have dR0 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2)) + ((2) * (D 0 t * D 2 t))) + ((1) * (D 1 t ^ 2))) ((((6*H₀^2*(Ω - 1)) * (D 0 t * D 1 t)) + ((2) * (D 0 t * D 3 t))) + ((4) * (D 1 t * D 2 t))) t := by
    filter_upwards [hder] with t ⟨h0, h1, h2, h3, h4, h5⟩
    exact (((((h0.pow 2).const_mul (3*H₀^2*(Ω - 1))).add ((h0.mul h2).const_mul (2))).add ((h1.pow 2).const_mul (1)))).congr_deriv (by (try simp only [Pi.pow_apply]); push_cast; ring)
  have dR1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((6*H₀^2*(Ω - 1)) * (D 0 t * D 1 t)) + ((2) * (D 0 t * D 3 t))) + ((4) * (D 1 t * D 2 t))) ((((((6*H₀^2*(Ω - 1)) * (D 0 t * D 2 t)) + ((2) * (D 0 t * D 4 t))) + ((6*H₀^2*(Ω - 1)) * (D 1 t ^ 2))) + ((6) * (D 1 t * D 3 t))) + ((4) * (D 2 t ^ 2))) t := by
    filter_upwards [hder] with t ⟨h0, h1, h2, h3, h4, h5⟩
    exact (((((h0.mul h1).const_mul (6*H₀^2*(Ω - 1))).add ((h0.mul h3).const_mul (2))).add ((h1.mul h2).const_mul (4)))).congr_deriv (by (try simp only [Pi.pow_apply]); push_cast; ring)
  have dR2 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((((6*H₀^2*(Ω - 1)) * (D 0 t * D 2 t)) + ((2) * (D 0 t * D 4 t))) + ((6*H₀^2*(Ω - 1)) * (D 1 t ^ 2))) + ((6) * (D 1 t * D 3 t))) + ((4) * (D 2 t ^ 2))) ((((((6*H₀^2*(Ω - 1)) * (D 0 t * D 3 t)) + ((2) * (D 0 t * D 5 t))) + ((18*H₀^2*(Ω - 1)) * (D 1 t * D 2 t))) + ((8) * (D 1 t * D 4 t))) + ((14) * (D 2 t * D 3 t))) t := by
    filter_upwards [hder] with t ⟨h0, h1, h2, h3, h4, h5⟩
    exact (((((((h0.mul h2).const_mul (6*H₀^2*(Ω - 1))).add ((h0.mul h4).const_mul (2))).add ((h1.pow 2).const_mul (6*H₀^2*(Ω - 1)))).add ((h1.mul h3).const_mul (6))).add ((h2.pow 2).const_mul (4)))).congr_deriv (by (try simp only [Pi.pow_apply]); push_cast; ring)
  have dR3 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((((6*H₀^2*(Ω - 1)) * (D 0 t * D 3 t)) + ((2) * (D 0 t * D 5 t))) + ((18*H₀^2*(Ω - 1)) * (D 1 t * D 2 t))) + ((8) * (D 1 t * D 4 t))) + ((14) * (D 2 t * D 3 t))) ((((((((6*H₀^2*(Ω - 1)) * (D 0 t * D 4 t)) + ((2) * (D 0 t * D 6 t))) + ((24*H₀^2*(Ω - 1)) * (D 1 t * D 3 t))) + ((10) * (D 1 t * D 5 t))) + ((18*H₀^2*(Ω - 1)) * (D 2 t ^ 2))) + ((22) * (D 2 t * D 4 t))) + ((14) * (D 3 t ^ 2))) t := by
    filter_upwards [hder] with t ⟨h0, h1, h2, h3, h4, h5⟩
    exact (((((((h0.mul h3).const_mul (6*H₀^2*(Ω - 1))).add ((h0.mul h5).const_mul (2))).add ((h1.mul h2).const_mul (18*H₀^2*(Ω - 1)))).add ((h1.mul h4).const_mul (8))).add ((h2.mul h3).const_mul (14)))).congr_deriv (by (try simp only [Pi.pow_apply]); push_cast; ring)

  have hD1 : ∀ᶠ t in 𝓝 t₀, D 1 t ≠ 0 := by
    have hc : ContinuousAt (D 1) t₀ := (cds t₀ hs).1.continuousAt
    have : (0 : ℝ) < D 1 t₀ := by rw [he1]; positivity
    filter_upwards [hc.eventually (lt_mem_nhds this)] with t ht using ht.ne'
  have hR0' : ∀ᶠ t in 𝓝 t₀, (((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2)) + ((2) * (D 0 t * D 2 t))) + ((1) * (D 1 t ^ 2)) = 0  := by
    filter_upwards [step hE dE, hD1] with t h1 h2
    exact (mul_eq_zero.1 h1).resolve_left h2
  have hR1' := step hR0' dR0
  have hR2' := step hR1' dR1
  have hR3' := step hR2' dR2
  have hR4' := step hR3' dR3
  have hR0 := hR0'.self_of_nhds
  have hR1 := hR1'.self_of_nhds
  have hR2 := hR2'.self_of_nhds
  have hR3 := hR3'.self_of_nhds
  have hR4 := hR4'.self_of_nhds
  have e2 : D 2 t₀ = (-a₀*H₀^2*(3*Ω - 2)/2) := by
    have : 2 * a₀ * (D 2 t₀ - (-a₀*H₀^2*(3*Ω - 2)/2)) = 0 := by linear_combination hR0 + (-3*a₀*H₀^2*Ω + 3*a₀*H₀^2 - 3*H₀^2*Ω*D 0 t₀ + 3*H₀^2*D 0 t₀ - 2*D 2 t₀) * he0 + (-a₀*H₀ - D 1 t₀) * he1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero ha0.ne')
    · linarith
  have he2 := e2
  have e3 : D 3 t₀ = (a₀*H₀^3) := by
    have : 2 * a₀ * (D 3 t₀ - (a₀*H₀^3)) = 0 := by linear_combination hR1 + (-2*(3*a₀*H₀^3*Ω - 3*a₀*H₀^3 + D 3 t₀)) * he0 + (-2*H₀^2*(-3*a₀*Ω + 2*a₀ + 3*Ω*D 0 t₀ - 3*D 0 t₀)) * he1 + (-4*D 1 t₀) * he2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero ha0.ne')
    · linarith
  have he3 := e3
  have e4 : D 4 t₀ = (-a₀*H₀^4*(9*Ω - 2)/2) := by
    have : 2 * a₀ * (D 4 t₀ - (-a₀*H₀^4*(9*Ω - 2)/2)) = 0 := by linear_combination hR2 + (9*a₀*H₀^4*Ω^2 - 15*a₀*H₀^4*Ω + 6*a₀*H₀^4 - 2*D 4 t₀) * he0 + (-6*H₀^2*(a₀*H₀*Ω + Ω*D 1 t₀ - D 1 t₀)) * he1 + (-2*(-3*a₀*H₀^2*Ω + 2*a₀*H₀^2 + 3*H₀^2*Ω*D 0 t₀ - 3*H₀^2*D 0 t₀ + 2*D 2 t₀)) * he2 + (-6*D 1 t₀) * he3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero ha0.ne')
    · linarith
  have he4 := e4
  have e5 : D 5 t₀ = (a₀*H₀^5*(27*Ω^2 + 6*Ω + 2)/2) := by
    have : 2 * a₀ * (D 5 t₀ - (a₀*H₀^5*(27*Ω^2 + 6*Ω + 2)/2)) = 0 := by linear_combination hR3 + (-2*(3*a₀*H₀^5*Ω - 3*a₀*H₀^5 + D 5 t₀)) * he0 + (a₀*H₀^4*(27*Ω^2 - 9*Ω + 10)) * he1 + (-2*H₀^2*(7*a₀*H₀ + 9*Ω*D 1 t₀ - 9*D 1 t₀)) * he2 + (-2*(3*H₀^2*Ω*D 0 t₀ - 3*H₀^2*D 0 t₀ + 7*D 2 t₀)) * he3 + (-8*D 1 t₀) * he4
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero ha0.ne')
    · linarith
  have he5 := e5
  have e6 : D 6 t₀ = (-a₀*H₀^6*(81*Ω^3 + 324*Ω^2 + 54*Ω - 4)/4) := by
    have : 2 * a₀ * (D 6 t₀ - (-a₀*H₀^6*(81*Ω^3 + 324*Ω^2 + 54*Ω - 4)/4)) = 0 := by linear_combination hR4 + (27*a₀*H₀^6*Ω^2 - 33*a₀*H₀^6*Ω + 6*a₀*H₀^6 - 2*D 6 t₀) * he0 + (-a₀*H₀^5*(135*Ω^2 + 54*Ω - 14)) * he1 + (-H₀^2*(-27*a₀*H₀^2*Ω^2 - 54*a₀*H₀^2*Ω + 4*a₀*H₀^2 + 18*Ω*D 2 t₀ - 18*D 2 t₀)) * he2 + (-2*(7*a₀*H₀^3 + 12*H₀^2*Ω*D 1 t₀ - 12*H₀^2*D 1 t₀ + 7*D 3 t₀)) * he3 + (-2*(3*H₀^2*Ω*D 0 t₀ - 3*H₀^2*D 0 t₀ + 11*D 2 t₀)) * he4 + (-10*D 1 t₀) * he5
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero ha0.ne')
    · linarith
  have he6 := e6
  have hH0 : H₀ ≠ 0 := hH.ne'
  have cc : ∀ n, cosmoCoeff n a t₀ = D n t₀ / (a₀ * H₀ ^ n) := fun n => by
    rw [cosmoCoeff, iteratedDeriv_eq_iterate]
  have hdec : decel a t₀ = -(D 2 t₀ * a₀) / D 1 t₀ ^ 2 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdec, e2, he1]; field_simp; try ring
  · rw [cc, e3]; field_simp
  · rw [cc, e4]; field_simp; try ring
  · rw [cc, e5]; field_simp; try ring
  · rw [cc, e6]; field_simp; try ring

end Work.Cosmography.Aviles

