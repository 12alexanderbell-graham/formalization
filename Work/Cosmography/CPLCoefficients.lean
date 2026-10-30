import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Checked.Cosmography.LCDMCoefficients

/-!
# Candidate C4: Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096, Eq. (22)

Source (typeset text verified in run 2026-10-30T0220Z by rendering the PDF, v1 and v2;
`runs/2026-10-30T0220Z/typeset/C4_cls2011_eq19_22_v*.png`; model sentence re-read from the PDF
text layer in run 2026-10-30T0430Z):
"w = w₀ + w_a (1 − a) = w₀ + w_a z (1+z)⁻¹ (16), so that, in a spatially flat universe filled
 with cold dark matter and dark energy, the dimensionless Hubble parameter E(z) = H/H₀ reads
 E²(z) = Ω_m (1+z)³ + Ω_X (1+z)^{3(1+w₀+w_a)} e^{−3 w_a z/(1+z)} (17)
 with Ω_X = 1 − Ω_m because of the flatness assumption. [...] Some algebra finally gives
 q₀ = 1/2 + 3/2 (1−Ω_m) w₀ (19), j₀ = 1 + 3/2 (1−Ω_m)[3w₀(1+w₀) + w_a] (20), s₀ = ... (21),
 l₀ = 35/2 + (1−Ω_m)/4 [213 + (7−Ω_m) w_a] w_a + (1−Ω_m)/4 [489 + 9(82 − 21Ω_m) w_a] w₀
      + 9/2 (1−Ω_m)[67 − 21Ω_m + 3/2 (23 − 11Ω_m) w_a] w₀² + 27/4 (1−Ω_m)(47 − 24Ω_m) w₀³
      + 81/2 (1−Ω_m)(3 − 2Ω_m) w₀⁴ (22)."
Definitions (their Eq. (2)): q = −ä/(aH²), j = a⁽³⁾/(aH³), s = a⁽⁴⁾/(aH⁴), l = a⁽⁵⁾/(aH⁵);
z := a(t₀)/a(t) − 1.

Conventions: as `Checked.Cosmography.Aviles` (`cosmoCoeff n a t = a⁽ⁿ⁾(t)/(a(t) H(t)ⁿ)`,
`hubble = ȧ/a`, `redshift a t₀ t = a(t₀)/a(t) − 1`). `IsFlatCPL Ω w₀ wₐ a t₀`: near t₀, a > 0,
a differentiable, and H(t) = H₀ √(E²(z(t))) with E² exactly Eq. (17), H₀ = H(t₀) > 0. The
power (1+z)^{3(1+w₀+wₐ)} is a real power of a positive number. No range of Ω, w₀, wₐ is
excluded.

FROZEN (annex 40.1) in run 2026-10-30T0430Z before proof work: `IsFlatCPL`, `CLSL0Claim`, and
the statements of `flatCPL_coeffs`, `printedL0_ne`, `clsL0Claim_false`.
-/

namespace Work.Cosmography.CPL

open Filter Topology Checked.Cosmography Checked.Cosmography.Aviles

/-- Flat matter + CPL dark energy (Capozziello–Lazkoz–Salzano Eq. (17)) at observation time
`t₀`: `H = H₀ √(Ω(1+z)³ + (1−Ω)(1+z)^{3(1+w₀+wₐ)} exp(−3wₐ z/(1+z)))` near `t₀`, `H₀ > 0`. -/
def IsFlatCPL (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 +
      (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) *
        Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))

/-- The printed claim for `l₀` (frozen verbatim from Eq. (22)). -/
def CLSL0Claim : Prop :=
  ∀ (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatCPL Ω w₀ wₐ a t₀ → ContDiffAt ℝ 5 a t₀ →
    cosmoCoeff 5 a t₀ = 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4

set_option maxHeartbeats 8000000 in
/-- **Cosmographic coefficients of flat matter + CPL** (correct version of CLS Eqs. (19)–(22)).
q₀, j₀ as printed; s₀ as printed with the dropped minus sign before `27/4` restored; l₀ with
`9 (7 − Ω)` in place of the printed `(7 − Ω)` in the `wₐ²` term. -/
theorem flatCPL_coeffs (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatCPL Ω w₀ wₐ a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    decel a t₀ = 1 / 2 + 3 / 2 * (1 - Ω) * w₀ ∧
    cosmoCoeff 3 a t₀ = 1 + 3 / 2 * (1 - Ω) * (3 * w₀ * (1 + w₀) + wₐ) ∧
    cosmoCoeff 4 a t₀ = -7 / 2 - 33 / 4 * (1 - Ω) * wₐ
      - 9 / 4 * (1 - Ω) * (9 + (7 - Ω) * wₐ) * w₀ - 9 / 4 * (1 - Ω) * (16 - 3 * Ω) * w₀ ^ 2
      - 27 / 4 * (1 - Ω) * (3 - Ω) * w₀ ^ 3 ∧
    cosmoCoeff 5 a t₀ = 35 / 2 + (1 - Ω) / 4 * (213 + 9 * (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := by
  obtain ⟨hH, hev⟩ := hL
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 3 * (1 + w₀ + wₐ) := ⟨_, rfl⟩
  set a₀ := a t₀ with ha₀
  set H₀ := hubble a t₀ with hH₀
  have ha0 : 0 < a₀ := hev.self_of_nhds.1
  set g : ℝ → ℝ := fun t => (a₀ / a t) ^ p * Real.exp (-3 * wₐ * (1 - a t / a₀)) with hgdef
  set D : ℕ → ℝ → ℝ := fun k => deriv^[k] a with hD
  set G : ℕ → ℝ → ℝ := fun k => deriv^[k] g with hG
  have hsm : ∀ᶠ t in 𝓝 t₀, ContDiffAt ℝ 5 a t := hs.eventually (by simp)
  have hpos : ∀ᶠ t in 𝓝 t₀, 0 < a t := hev.mono fun t h => h.1
  have gsm : ∀ t, ContDiffAt ℝ 5 a t → 0 < a t → ContDiffAt ℝ 5 g t := by
    intro t h hat
    exact ((contDiffAt_const.div h hat.ne').rpow_const_of_ne (div_pos ha0 hat).ne').mul
      ((contDiffAt_const.mul (contDiffAt_const.sub (h.div_const _))).exp)
  have hgsm : ∀ᶠ t in 𝓝 t₀, ContDiffAt ℝ 5 g t := by
    filter_upwards [hsm, hpos] with t h hat using gsm t h hat
  have key : ∀ (f : ℝ → ℝ) k t, DifferentiableAt ℝ (deriv^[k] f) t →
      HasDerivAt (deriv^[k] f) (deriv^[k+1] f t) t := by
    intro f k t hk
    simpa [Function.iterate_succ_apply'] using hk.hasDerivAt
  have cds : ∀ (f : ℝ → ℝ) t, ContDiffAt ℝ 5 f t →
      DifferentiableAt ℝ (deriv^[0] f) t ∧ DifferentiableAt ℝ (deriv^[1] f) t ∧
      DifferentiableAt ℝ (deriv^[2] f) t ∧ DifferentiableAt ℝ (deriv^[3] f) t ∧
      DifferentiableAt ℝ (deriv^[4] f) t := by
    intro f t h
    have c4 : ContDiffAt ℝ 4 (deriv^[1] f) t := h.derivWithin (by norm_num)
    have c3 : ContDiffAt ℝ 3 (deriv^[2] f) t := by
      have := c4.derivWithin (m := 3) (by norm_num)
      simpa [Function.iterate_succ_apply'] using this
    have c2 : ContDiffAt ℝ 2 (deriv^[3] f) t := by
      have := c3.derivWithin (m := 2) (by norm_num)
      simpa [Function.iterate_succ_apply'] using this
    have c1 : ContDiffAt ℝ 1 (deriv^[4] f) t := by
      have := c2.derivWithin (m := 1) (by norm_num)
      simpa [Function.iterate_succ_apply'] using this
    exact ⟨h.differentiableAt (by norm_num), c4.differentiableAt (by norm_num),
      c3.differentiableAt (by norm_num), c2.differentiableAt (by norm_num),
      c1.differentiableAt (by norm_num)⟩
  have hder : ∀ᶠ t in 𝓝 t₀, HasDerivAt (D 0) (D 1 t) t ∧ HasDerivAt (D 1) (D 2 t) t ∧
      HasDerivAt (D 2) (D 3 t) t ∧ HasDerivAt (D 3) (D 4 t) t ∧ HasDerivAt (D 4) (D 5 t) t ∧
      HasDerivAt (G 0) (G 1 t) t ∧ HasDerivAt (G 1) (G 2 t) t ∧
      HasDerivAt (G 2) (G 3 t) t ∧ HasDerivAt (G 3) (G 4 t) t := by
    filter_upwards [hsm, hgsm] with t h hg'
    obtain ⟨a0, a1, a2, a3, a4⟩ := cds a t h
    obtain ⟨g0, g1, g2, g3, -⟩ := cds g t hg'
    exact ⟨key a 0 t a0, key a 1 t a1, key a 2 t a2, key a 3 t a3, key a 4 t a4,
      key g 0 t g0, key g 1 t g1, key g 2 t g2, key g 3 t g3⟩
  have he_d0 : D 0 t₀ = a₀ := rfl
  have he_d1 : D 1 t₀ = H₀ * a₀ := by
    have h1 : D 1 t₀ = deriv a t₀ := rfl
    rw [h1, hH₀, hubble, ← ha₀]
    field_simp
  have he_g0 : G 0 t₀ = 1 := by
    simp only [hG, hgdef, Function.iterate_zero, id, ← ha₀, div_self ha0.ne', Real.one_rpow,
      sub_self, mul_zero, Real.exp_zero, mul_one]
  -- the model, polynomial form
  have hgc : ContinuousAt g t₀ := (gsm t₀ hs ha0).continuousAt
  have harg : ∀ᶠ t in 𝓝 t₀, 0 < Ω * (a₀ / a t) ^ 3 + (1 - Ω) * g t := by
    have hc : ContinuousAt (fun t => Ω * (a₀ / a t) ^ 3 + (1 - Ω) * g t) t₀ := by
      have : ContinuousAt a t₀ := hs.continuousAt
      exact ((continuousAt_const.div this ha0.ne').pow 3 |>.const_mul Ω).add
        (hgc.const_mul _)
    have h1 : (0 : ℝ) < Ω * (a₀ / a t₀) ^ 3 + (1 - Ω) * g t₀ := by
      have : g t₀ = 1 := he_g0
      rw [this, ← ha₀, div_self ha0.ne']; norm_num
    exact hc.eventually (lt_mem_nhds h1)
  have hE0 : ∀ᶠ t in 𝓝 t₀, a t * deriv a t ^ 2 -
      H₀ ^ 2 * (Ω * a₀ ^ 3 + (1 - Ω) * a t ^ 3 * g t) = 0 := by
    filter_upwards [hev, harg] with t ⟨hat, _, hHt⟩ hS
    have hz : 1 + redshift a t₀ t = a₀ / a t := by rw [redshift, add_sub_cancel]
    have hexp : -(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t) = -3 * wₐ * (1 - a t / a₀) := by
      rw [hz, redshift]; field_simp; ring
    rw [hexp, hz, ← hp] at hHt
    have hg' : (a₀ / a t) ^ p * Real.exp (-3 * wₐ * (1 - a t / a₀)) = g t := rfl
    rw [mul_assoc (1 - Ω), hg'] at hHt
    have hsq := congrArg (fun x => x ^ 2) hHt
    simp only [hubble, mul_pow, Real.sq_sqrt hS.le] at hsq
    rw [div_pow, div_eq_iff (pow_pos hat 2).ne'] at hsq
    rw [hsq, div_pow]
    field_simp
    ring
  have hE1 : ∀ᶠ t in 𝓝 t₀, a₀ * a t * deriv g t + p * a₀ * g t * deriv a t -
      3 * wₐ * a t * g t * deriv a t = 0 := by
    filter_upwards [hev] with t ⟨hat, hda, _⟩
    have hq : 0 < a₀ / a t := by positivity
    have h1 : HasDerivAt (fun t => a₀ / a t) ((0 * a t - a₀ * deriv a t) / a t ^ 2) t :=
      (hasDerivAt_const t a₀).div hda.hasDerivAt hat.ne'
    have h2 := h1.rpow_const (p := p) (Or.inl hq.ne')
    have h3 : HasDerivAt (fun t => -3 * wₐ * (1 - a t / a₀))
        (-3 * wₐ * (-(deriv a t / a₀))) t :=
      ((hda.hasDerivAt.div_const a₀).const_sub 1).const_mul _
    have h4 := h2.mul h3.exp
    have hgd : deriv g t = _ := h4.deriv
    rw [hgd, Real.rpow_sub_one hq.ne']
    simp only [g]
    field_simp
    ring
  -- GENERATED: zero functions
  have hF0_0 : ∀ᶠ t in 𝓝 t₀, (((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 0 t)) + ((1) * (D 0 t * D 1 t ^ 2))) + ((-a₀^3*H₀^2*Ω)) = 0 := by
    filter_upwards [hE0] with t h
    simp only [hD, hG, Function.iterate_zero, Function.iterate_one, id]
    linear_combination h
  have hF1_0 : ∀ᶠ t in 𝓝 t₀, (((-3*wₐ) * (D 0 t * D 1 t * G 0 t)) + ((a₀) * (D 0 t * G 1 t))) + ((a₀*p) * (D 1 t * G 0 t)) = 0 := by
    filter_upwards [hE1] with t h
    simp only [hD, hG, Function.iterate_zero, Function.iterate_one, id]
    linear_combination h
  have dF0_0 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 0 t)) + ((1) * (D 0 t * D 1 t ^ 2))) + ((-a₀^3*H₀^2*Ω))) (((((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 1 t)) + ((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 1 t * G 0 t))) + ((2) * (D 0 t * D 1 t * D 2 t))) + ((1) * (D 1 t ^ 3))) t := by
    filter_upwards [hder] with t ⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩
    exact ((((((hd0.pow 3).mul hg0).const_mul (H₀^2*(Ω - 1))).add ((hd0.mul (hd1.pow 2)).const_mul (1))).add (hasDerivAt_const t (-a₀^3*H₀^2*Ω)))).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)
  have dF0_1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => ((((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 1 t)) + ((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 1 t * G 0 t))) + ((2) * (D 0 t * D 1 t * D 2 t))) + ((1) * (D 1 t ^ 3))) ((((((((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 2 t)) + ((6*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 1 t * G 1 t))) + ((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 2 t * G 0 t))) + ((6*H₀^2*(Ω - 1)) * (D 0 t * D 1 t ^ 2 * G 0 t))) + ((2) * (D 0 t * D 1 t * D 3 t))) + ((2) * (D 0 t * D 2 t ^ 2))) + ((5) * (D 1 t ^ 2 * D 2 t))) t := by
    filter_upwards [hder] with t ⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩
    exact (((((((hd0.pow 3).mul hg1).const_mul (H₀^2*(Ω - 1))).add ((((hd0.pow 2).mul hd1).mul hg0).const_mul (3*H₀^2*(Ω - 1)))).add (((hd0.mul hd1).mul hd2).const_mul (2))).add ((hd1.pow 3).const_mul (1)))).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)
  have dF0_2 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((((((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 2 t)) + ((6*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 1 t * G 1 t))) + ((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 2 t * G 0 t))) + ((6*H₀^2*(Ω - 1)) * (D 0 t * D 1 t ^ 2 * G 0 t))) + ((2) * (D 0 t * D 1 t * D 3 t))) + ((2) * (D 0 t * D 2 t ^ 2))) + ((5) * (D 1 t ^ 2 * D 2 t))) ((((((((((((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 3 t)) + ((9*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 1 t * G 2 t))) + ((9*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 2 t * G 1 t))) + ((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 3 t * G 0 t))) + ((18*H₀^2*(Ω - 1)) * (D 0 t * D 1 t ^ 2 * G 1 t))) + ((18*H₀^2*(Ω - 1)) * (D 0 t * D 1 t * D 2 t * G 0 t))) + ((2) * (D 0 t * D 1 t * D 4 t))) + ((6) * (D 0 t * D 2 t * D 3 t))) + ((6*H₀^2*(Ω - 1)) * (D 1 t ^ 3 * G 0 t))) + ((7) * (D 1 t ^ 2 * D 3 t))) + ((12) * (D 1 t * D 2 t ^ 2))) t := by
    filter_upwards [hder] with t ⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩
    exact ((((((((((hd0.pow 3).mul hg2).const_mul (H₀^2*(Ω - 1))).add ((((hd0.pow 2).mul hd1).mul hg1).const_mul (6*H₀^2*(Ω - 1)))).add ((((hd0.pow 2).mul hd2).mul hg0).const_mul (3*H₀^2*(Ω - 1)))).add (((hd0.mul (hd1.pow 2)).mul hg0).const_mul (6*H₀^2*(Ω - 1)))).add (((hd0.mul hd1).mul hd3).const_mul (2))).add ((hd0.mul (hd2.pow 2)).const_mul (2))).add (((hd1.pow 2).mul hd2).const_mul (5)))).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)
  have dF0_3 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((((((((((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 3 t)) + ((9*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 1 t * G 2 t))) + ((9*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 2 t * G 1 t))) + ((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 3 t * G 0 t))) + ((18*H₀^2*(Ω - 1)) * (D 0 t * D 1 t ^ 2 * G 1 t))) + ((18*H₀^2*(Ω - 1)) * (D 0 t * D 1 t * D 2 t * G 0 t))) + ((2) * (D 0 t * D 1 t * D 4 t))) + ((6) * (D 0 t * D 2 t * D 3 t))) + ((6*H₀^2*(Ω - 1)) * (D 1 t ^ 3 * G 0 t))) + ((7) * (D 1 t ^ 2 * D 3 t))) + ((12) * (D 1 t * D 2 t ^ 2))) ((((((((((((((((((H₀^2*(Ω - 1)) * (D 0 t ^ 3 * G 4 t)) + ((12*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 1 t * G 3 t))) + ((18*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 2 t * G 2 t))) + ((12*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 3 t * G 1 t))) + ((3*H₀^2*(Ω - 1)) * (D 0 t ^ 2 * D 4 t * G 0 t))) + ((36*H₀^2*(Ω - 1)) * (D 0 t * D 1 t ^ 2 * G 2 t))) + ((72*H₀^2*(Ω - 1)) * (D 0 t * D 1 t * D 2 t * G 1 t))) + ((24*H₀^2*(Ω - 1)) * (D 0 t * D 1 t * D 3 t * G 0 t))) + ((2) * (D 0 t * D 1 t * D 5 t))) + ((18*H₀^2*(Ω - 1)) * (D 0 t * D 2 t ^ 2 * G 0 t))) + ((8) * (D 0 t * D 2 t * D 4 t))) + ((6) * (D 0 t * D 3 t ^ 2))) + ((24*H₀^2*(Ω - 1)) * (D 1 t ^ 3 * G 1 t))) + ((36*H₀^2*(Ω - 1)) * (D 1 t ^ 2 * D 2 t * G 0 t))) + ((9) * (D 1 t ^ 2 * D 4 t))) + ((44) * (D 1 t * D 2 t * D 3 t))) + ((12) * (D 2 t ^ 3))) t := by
    filter_upwards [hder] with t ⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩
    exact ((((((((((((((hd0.pow 3).mul hg3).const_mul (H₀^2*(Ω - 1))).add ((((hd0.pow 2).mul hd1).mul hg2).const_mul (9*H₀^2*(Ω - 1)))).add ((((hd0.pow 2).mul hd2).mul hg1).const_mul (9*H₀^2*(Ω - 1)))).add ((((hd0.pow 2).mul hd3).mul hg0).const_mul (3*H₀^2*(Ω - 1)))).add (((hd0.mul (hd1.pow 2)).mul hg1).const_mul (18*H₀^2*(Ω - 1)))).add ((((hd0.mul hd1).mul hd2).mul hg0).const_mul (18*H₀^2*(Ω - 1)))).add (((hd0.mul hd1).mul hd4).const_mul (2))).add (((hd0.mul hd2).mul hd3).const_mul (6))).add (((hd1.pow 3).mul hg0).const_mul (6*H₀^2*(Ω - 1)))).add (((hd1.pow 2).mul hd3).const_mul (7))).add ((hd1.mul (hd2.pow 2)).const_mul (12)))).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)
  have dF1_0 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((-3*wₐ) * (D 0 t * D 1 t * G 0 t)) + ((a₀) * (D 0 t * G 1 t))) + ((a₀*p) * (D 1 t * G 0 t))) (((((((-3*wₐ) * (D 0 t * D 1 t * G 1 t)) + ((-3*wₐ) * (D 0 t * D 2 t * G 0 t))) + ((a₀) * (D 0 t * G 2 t))) + ((-3*wₐ) * (D 1 t ^ 2 * G 0 t))) + ((a₀*(p + 1)) * (D 1 t * G 1 t))) + ((a₀*p) * (D 2 t * G 0 t))) t := by
    filter_upwards [hder] with t ⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩
    exact ((((((hd0.mul hd1).mul hg0).const_mul (-3*wₐ)).add ((hd0.mul hg1).const_mul (a₀))).add ((hd1.mul hg0).const_mul (a₀*p)))).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)
  have dF1_1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => ((((((-3*wₐ) * (D 0 t * D 1 t * G 1 t)) + ((-3*wₐ) * (D 0 t * D 2 t * G 0 t))) + ((a₀) * (D 0 t * G 2 t))) + ((-3*wₐ) * (D 1 t ^ 2 * G 0 t))) + ((a₀*(p + 1)) * (D 1 t * G 1 t))) + ((a₀*p) * (D 2 t * G 0 t))) ((((((((((-3*wₐ) * (D 0 t * D 1 t * G 2 t)) + ((-6*wₐ) * (D 0 t * D 2 t * G 1 t))) + ((-3*wₐ) * (D 0 t * D 3 t * G 0 t))) + ((a₀) * (D 0 t * G 3 t))) + ((-6*wₐ) * (D 1 t ^ 2 * G 1 t))) + ((-9*wₐ) * (D 1 t * D 2 t * G 0 t))) + ((a₀*(p + 2)) * (D 1 t * G 2 t))) + ((a₀*(2*p + 1)) * (D 2 t * G 1 t))) + ((a₀*p) * (D 3 t * G 0 t))) t := by
    filter_upwards [hder] with t ⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩
    exact (((((((((hd0.mul hd1).mul hg1).const_mul (-3*wₐ)).add (((hd0.mul hd2).mul hg0).const_mul (-3*wₐ))).add ((hd0.mul hg2).const_mul (a₀))).add (((hd1.pow 2).mul hg0).const_mul (-3*wₐ))).add ((hd1.mul hg1).const_mul (a₀*(p + 1)))).add ((hd2.mul hg0).const_mul (a₀*p)))).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)
  have dF1_2 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => (((((((((-3*wₐ) * (D 0 t * D 1 t * G 2 t)) + ((-6*wₐ) * (D 0 t * D 2 t * G 1 t))) + ((-3*wₐ) * (D 0 t * D 3 t * G 0 t))) + ((a₀) * (D 0 t * G 3 t))) + ((-6*wₐ) * (D 1 t ^ 2 * G 1 t))) + ((-9*wₐ) * (D 1 t * D 2 t * G 0 t))) + ((a₀*(p + 2)) * (D 1 t * G 2 t))) + ((a₀*(2*p + 1)) * (D 2 t * G 1 t))) + ((a₀*p) * (D 3 t * G 0 t))) ((((((((((((((-3*wₐ) * (D 0 t * D 1 t * G 3 t)) + ((-9*wₐ) * (D 0 t * D 2 t * G 2 t))) + ((-9*wₐ) * (D 0 t * D 3 t * G 1 t))) + ((-3*wₐ) * (D 0 t * D 4 t * G 0 t))) + ((a₀) * (D 0 t * G 4 t))) + ((-9*wₐ) * (D 1 t ^ 2 * G 2 t))) + ((-27*wₐ) * (D 1 t * D 2 t * G 1 t))) + ((-12*wₐ) * (D 1 t * D 3 t * G 0 t))) + ((a₀*(p + 3)) * (D 1 t * G 3 t))) + ((-9*wₐ) * (D 2 t ^ 2 * G 0 t))) + ((3*a₀*(p + 1)) * (D 2 t * G 2 t))) + ((a₀*(3*p + 1)) * (D 3 t * G 1 t))) + ((a₀*p) * (D 4 t * G 0 t))) t := by
    filter_upwards [hder] with t ⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩
    exact ((((((((((((hd0.mul hd1).mul hg2).const_mul (-3*wₐ)).add (((hd0.mul hd2).mul hg1).const_mul (-6*wₐ))).add (((hd0.mul hd3).mul hg0).const_mul (-3*wₐ))).add ((hd0.mul hg3).const_mul (a₀))).add (((hd1.pow 2).mul hg1).const_mul (-6*wₐ))).add (((hd1.mul hd2).mul hg0).const_mul (-9*wₐ))).add ((hd1.mul hg2).const_mul (a₀*(p + 2)))).add ((hd2.mul hg1).const_mul (a₀*(2*p + 1)))).add ((hd3.mul hg0).const_mul (a₀*p)))).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)
  have hF0_1 := step hF0_0 dF0_0
  have hF0_2 := step hF0_1 dF0_1
  have hF0_3 := step hF0_2 dF0_2
  have hF0_4 := step hF0_3 dF0_3
  have hF1_1 := step hF1_0 dF1_0
  have hF1_2 := step hF1_1 dF1_1
  have hF1_3 := step hF1_2 dF1_2
  have z0_0 := hF0_0.self_of_nhds
  have z0_1 := hF0_1.self_of_nhds
  have z0_2 := hF0_2.self_of_nhds
  have z0_3 := hF0_3.self_of_nhds
  have z0_4 := hF0_4.self_of_nhds
  have z1_0 := hF1_0.self_of_nhds
  have z1_1 := hF1_1.self_of_nhds
  have z1_2 := hF1_2.self_of_nhds
  have z1_3 := hF1_3.self_of_nhds
  have he_g1 : G 1 t₀ = H₀*(3*wₐ - p) := by
    have h : (a₀^2) * (G 1 t₀ - (H₀*(3*wₐ - p))) = 0 := by
      linear_combination z1_0 - (-3*a₀*H₀*wₐ + a₀*G 1 t₀) * he_d0 - (a₀*p - 3*wₐ*D 0 t₀) * he_d1 - (a₀*p*D 1 t₀ - 3*wₐ*D 0 t₀*D 1 t₀) * he_g0
    have hl : (a₀^2) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have he_d2 : D 2 t₀ = -a₀*H₀^2*(3*wₐ*Ω - 3*wₐ - p*Ω + p + 3*Ω - 2)/2 := by
    have h : (2*a₀^2*H₀) * (D 2 t₀ - (-a₀*H₀^2*(3*wₐ*Ω - 3*wₐ - p*Ω + p + 3*Ω - 2)/2)) = 0 := by
      linear_combination z0_1 - (3*a₀^2*H₀^3*wₐ*Ω - 3*a₀^2*H₀^3*wₐ - a₀^2*H₀^3*p*Ω + a₀^2*H₀^3*p + 3*a₀^2*H₀^3*Ω - 3*a₀^2*H₀^3 + 3*a₀*H₀^3*wₐ*Ω*D 0 t₀ - 3*a₀*H₀^3*wₐ*D 0 t₀ - a₀*H₀^3*p*Ω*D 0 t₀ + a₀*H₀^3*p*D 0 t₀ + 3*a₀*H₀^3*Ω*D 0 t₀ - 3*a₀*H₀^3*D 0 t₀ + 2*a₀*H₀*D 2 t₀ + 3*H₀^3*wₐ*Ω*D 0 t₀^2 - 3*H₀^3*wₐ*D 0 t₀^2 - H₀^3*p*Ω*D 0 t₀^2 + H₀^3*p*D 0 t₀^2) * he_d0 - (a₀^2*H₀^2 + a₀*H₀*D 1 t₀ + 3*H₀^2*Ω*D 0 t₀^2 - 3*H₀^2*D 0 t₀^2 + 2*D 0 t₀*D 2 t₀ + D 1 t₀^2) * he_d1 - (3*H₀^2*Ω*D 0 t₀^2*D 1 t₀ - 3*H₀^2*D 0 t₀^2*D 1 t₀) * he_g0 - (H₀^2*Ω*D 0 t₀^3 - H₀^2*D 0 t₀^3) * he_g1
    have hl : (2*a₀^2*H₀) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have he_g2 : G 2 t₀ = -H₀^2*(9*wₐ^2*Ω - 27*wₐ^2 - 6*wₐ*p*Ω + 18*wₐ*p + 9*wₐ*Ω - 6*wₐ + p^2*Ω - 3*p^2 - 3*p*Ω)/2 := by
    have h : (a₀^2) * (G 2 t₀ - (-H₀^2*(9*wₐ^2*Ω - 27*wₐ^2 - 6*wₐ*p*Ω + 18*wₐ*p + 9*wₐ*Ω - 6*wₐ + p^2*Ω - 3*p^2 - 3*p*Ω)/2)) = 0 := by
      linear_combination z1_1 - (9*a₀*H₀^2*wₐ^2*Ω/2 - 27*a₀*H₀^2*wₐ^2/2 - 3*a₀*H₀^2*wₐ*p*Ω/2 + 9*a₀*H₀^2*wₐ*p/2 + 9*a₀*H₀^2*wₐ*Ω/2 - 3*a₀*H₀^2*wₐ + a₀*G 2 t₀) * he_d0 - (3*a₀*H₀*wₐ*p - a₀*H₀*p^2 - a₀*H₀*p - 9*H₀*wₐ^2*D 0 t₀ + 3*H₀*wₐ*p*D 0 t₀ - 3*wₐ*D 1 t₀) * he_d1 - (-3*a₀^2*H₀^2*wₐ*p*Ω/2 + 3*a₀^2*H₀^2*wₐ*p/2 + a₀^2*H₀^2*p^2*Ω/2 - a₀^2*H₀^2*p^2/2 - 3*a₀^2*H₀^2*p*Ω/2 + a₀^2*H₀^2*p + 9*a₀*H₀^2*wₐ^2*Ω*D 0 t₀/2 - 9*a₀*H₀^2*wₐ^2*D 0 t₀/2 - 3*a₀*H₀^2*wₐ*p*Ω*D 0 t₀/2 + 3*a₀*H₀^2*wₐ*p*D 0 t₀/2 + 9*a₀*H₀^2*wₐ*Ω*D 0 t₀/2 - 3*a₀*H₀^2*wₐ*D 0 t₀ - 3*wₐ*D 1 t₀^2) * he_g0 - (a₀*p*D 1 t₀ + a₀*D 1 t₀ - 3*wₐ*D 0 t₀*D 1 t₀) * he_g1 - (a₀*p*G 0 t₀ - 3*wₐ*D 0 t₀*G 0 t₀) * he_d2
    have hl : (a₀^2) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have he_d3 : D 3 t₀ = -a₀*H₀^3*(9*wₐ^2*Ω - 9*wₐ^2 - 6*wₐ*p*Ω + 6*wₐ*p + 12*wₐ*Ω - 12*wₐ + p^2*Ω - p^2 - 3*p*Ω + 3*p - 2)/2 := by
    have h : (2*a₀^2*H₀) * (D 3 t₀ - (-a₀*H₀^3*(9*wₐ^2*Ω - 9*wₐ^2 - 6*wₐ*p*Ω + 6*wₐ*p + 12*wₐ*Ω - 12*wₐ + p^2*Ω - p^2 - 3*p*Ω + 3*p - 2)/2)) = 0 := by
      linear_combination z0_2 - (9*a₀^2*H₀^4*wₐ^2*Ω - 9*a₀^2*H₀^4*wₐ^2 - 6*a₀^2*H₀^4*wₐ*p*Ω + 6*a₀^2*H₀^4*wₐ*p + 39*a₀^2*H₀^4*wₐ*Ω/2 - 39*a₀^2*H₀^4*wₐ/2 + a₀^2*H₀^4*p^2*Ω - a₀^2*H₀^4*p^2 - 11*a₀^2*H₀^4*p*Ω/2 + 11*a₀^2*H₀^4*p/2 + 15*a₀^2*H₀^4*Ω/2 - 7*a₀^2*H₀^4 - 9*a₀*H₀^4*wₐ^2*Ω^2*D 0 t₀/2 + 18*a₀*H₀^4*wₐ^2*Ω*D 0 t₀ - 27*a₀*H₀^4*wₐ^2*D 0 t₀/2 + 3*a₀*H₀^4*wₐ*p*Ω^2*D 0 t₀ - 12*a₀*H₀^4*wₐ*p*Ω*D 0 t₀ + 9*a₀*H₀^4*wₐ*p*D 0 t₀ - 9*a₀*H₀^4*wₐ*Ω^2*D 0 t₀ + 69*a₀*H₀^4*wₐ*Ω*D 0 t₀/2 - 51*a₀*H₀^4*wₐ*D 0 t₀/2 - a₀*H₀^4*p^2*Ω^2*D 0 t₀/2 + 2*a₀*H₀^4*p^2*Ω*D 0 t₀ - 3*a₀*H₀^4*p^2*D 0 t₀/2 + 3*a₀*H₀^4*p*Ω^2*D 0 t₀ - 21*a₀*H₀^4*p*Ω*D 0 t₀/2 + 15*a₀*H₀^4*p*D 0 t₀/2 - 9*a₀*H₀^4*Ω^2*D 0 t₀/2 + 15*a₀*H₀^4*Ω*D 0 t₀/2 - 3*a₀*H₀^4*D 0 t₀ + 2*a₀*H₀*D 3 t₀ - 9*H₀^4*wₐ^2*Ω^2*D 0 t₀^2/2 + 18*H₀^4*wₐ^2*Ω*D 0 t₀^2 - 27*H₀^4*wₐ^2*D 0 t₀^2/2 + 3*H₀^4*wₐ*p*Ω^2*D 0 t₀^2 - 12*H₀^4*wₐ*p*Ω*D 0 t₀^2 + 9*H₀^4*wₐ*p*D 0 t₀^2 - 9*H₀^4*wₐ*Ω^2*D 0 t₀^2/2 + 15*H₀^4*wₐ*Ω*D 0 t₀^2/2 - 3*H₀^4*wₐ*D 0 t₀^2 - H₀^4*p^2*Ω^2*D 0 t₀^2/2 + 2*H₀^4*p^2*Ω*D 0 t₀^2 - 3*H₀^4*p^2*D 0 t₀^2/2 + 3*H₀^4*p*Ω^2*D 0 t₀^2/2 - 3*H₀^4*p*Ω*D 0 t₀^2/2) * he_d0 - (-15*a₀^2*H₀^3*wₐ*Ω/2 + 15*a₀^2*H₀^3*wₐ/2 + 5*a₀^2*H₀^3*p*Ω/2 - 5*a₀^2*H₀^3*p/2 - 15*a₀^2*H₀^3*Ω/2 + 5*a₀^2*H₀^3 + 6*a₀*H₀^3*Ω*D 0 t₀ - 6*a₀*H₀^3*D 0 t₀ - 15*a₀*H₀^2*wₐ*Ω*D 1 t₀/2 + 15*a₀*H₀^2*wₐ*D 1 t₀/2 + 5*a₀*H₀^2*p*Ω*D 1 t₀/2 - 5*a₀*H₀^2*p*D 1 t₀/2 - 15*a₀*H₀^2*Ω*D 1 t₀/2 + 5*a₀*H₀^2*D 1 t₀ + 18*H₀^3*wₐ*Ω*D 0 t₀^2 - 18*H₀^3*wₐ*D 0 t₀^2 - 6*H₀^3*p*Ω*D 0 t₀^2 + 6*H₀^3*p*D 0 t₀^2 + 6*H₀^2*Ω*D 0 t₀*D 1 t₀ - 6*H₀^2*D 0 t₀*D 1 t₀ + 2*D 0 t₀*D 3 t₀) * he_d1 - (-9*a₀*H₀^4*wₐ*Ω^2*D 0 t₀^2/2 + 9*a₀*H₀^4*wₐ*Ω*D 0 t₀^2 - 9*a₀*H₀^4*wₐ*D 0 t₀^2/2 + 3*a₀*H₀^4*p*Ω^2*D 0 t₀^2/2 - 3*a₀*H₀^4*p*Ω*D 0 t₀^2 + 3*a₀*H₀^4*p*D 0 t₀^2/2 - 9*a₀*H₀^4*Ω^2*D 0 t₀^2/2 + 15*a₀*H₀^4*Ω*D 0 t₀^2/2 - 3*a₀*H₀^4*D 0 t₀^2 + 6*H₀^2*Ω*D 0 t₀*D 1 t₀^2 - 6*H₀^2*D 0 t₀*D 1 t₀^2) * he_g0 - (6*H₀^2*Ω*D 0 t₀^2*D 1 t₀ - 6*H₀^2*D 0 t₀^2*D 1 t₀) * he_g1 - (-3*a₀*H₀^2*wₐ*Ω*D 0 t₀ + 3*a₀*H₀^2*wₐ*D 0 t₀ + a₀*H₀^2*p*Ω*D 0 t₀ - a₀*H₀^2*p*D 0 t₀ - 3*a₀*H₀^2*Ω*D 0 t₀ + 2*a₀*H₀^2*D 0 t₀ + 3*H₀^2*Ω*D 0 t₀^2*G 0 t₀ - 3*H₀^2*D 0 t₀^2*G 0 t₀ + 2*D 0 t₀*D 2 t₀ + 5*D 1 t₀^2) * he_d2 - (H₀^2*Ω*D 0 t₀^3 - H₀^2*D 0 t₀^3) * he_g2
    have hl : (2*a₀^2*H₀) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have he_g3 : G 3 t₀ = -H₀^3*(108*wₐ^3*Ω - 162*wₐ^3 - 108*wₐ^2*p*Ω + 162*wₐ^2*p + 117*wₐ^2*Ω - 90*wₐ^2 + 36*wₐ*p^2*Ω - 54*wₐ*p^2 - 66*wₐ*p*Ω + 30*wₐ*p - 6*wₐ - 4*p^3*Ω + 6*p^3 + 9*p^2*Ω + 9*p*Ω)/2 := by
    have h : (a₀^2) * (G 3 t₀ - (-H₀^3*(108*wₐ^3*Ω - 162*wₐ^3 - 108*wₐ^2*p*Ω + 162*wₐ^2*p + 117*wₐ^2*Ω - 90*wₐ^2 + 36*wₐ*p^2*Ω - 54*wₐ*p^2 - 66*wₐ*p*Ω + 30*wₐ*p - 6*wₐ - 4*p^3*Ω + 6*p^3 + 9*p^2*Ω + 9*p*Ω)/2)) = 0 := by
      linear_combination z1_2 - (54*a₀*H₀^3*wₐ^3*Ω - 81*a₀*H₀^3*wₐ^3 - 36*a₀*H₀^3*wₐ^2*p*Ω + 54*a₀*H₀^3*wₐ^2*p + 117*a₀*H₀^3*wₐ^2*Ω/2 - 45*a₀*H₀^3*wₐ^2 + 6*a₀*H₀^3*wₐ*p^2*Ω - 9*a₀*H₀^3*wₐ*p^2 - 18*a₀*H₀^3*wₐ*p*Ω + 21*a₀*H₀^3*wₐ*p/2 - 3*a₀*H₀^3*wₐ + a₀*G 3 t₀) * he_d0 - (-9*a₀*H₀^2*wₐ^2*p*Ω/2 + 27*a₀*H₀^2*wₐ^2*p/2 + 9*a₀*H₀^2*wₐ^2*Ω/2 - 9*a₀*H₀^2*wₐ^2/2 + 3*a₀*H₀^2*wₐ*p^2*Ω - 9*a₀*H₀^2*wₐ*p^2 - 3*a₀*H₀^2*wₐ*p*Ω - 9*a₀*H₀^2*wₐ*p/2 + 9*a₀*H₀^2*wₐ*Ω/2 - 3*a₀*H₀^2*wₐ - a₀*H₀^2*p^3*Ω/2 + 3*a₀*H₀^2*p^3/2 + a₀*H₀^2*p^2*Ω/2 + 3*a₀*H₀^2*p^2 + 3*a₀*H₀^2*p*Ω + 27*H₀^2*wₐ^3*Ω*D 0 t₀/2 - 81*H₀^2*wₐ^3*D 0 t₀/2 - 9*H₀^2*wₐ^2*p*Ω*D 0 t₀ + 27*H₀^2*wₐ^2*p*D 0 t₀ + 27*H₀^2*wₐ^2*Ω*D 0 t₀/2 - 9*H₀^2*wₐ^2*D 0 t₀ + 3*H₀^2*wₐ*p^2*Ω*D 0 t₀/2 - 9*H₀^2*wₐ*p^2*D 0 t₀/2 - 9*H₀^2*wₐ*p*Ω*D 0 t₀/2 - 18*H₀*wₐ^2*D 1 t₀ + 6*H₀*wₐ*p*D 1 t₀) * he_d1 - (-9*a₀^2*H₀^3*wₐ^2*p*Ω/2 + 9*a₀^2*H₀^3*wₐ^2*p/2 + 3*a₀^2*H₀^3*wₐ*p^2*Ω - 3*a₀^2*H₀^3*wₐ*p^2 - 6*a₀^2*H₀^3*wₐ*p*Ω + 6*a₀^2*H₀^3*wₐ*p - a₀^2*H₀^3*p^3*Ω/2 + a₀^2*H₀^3*p^3/2 + 3*a₀^2*H₀^3*p^2*Ω/2 - 3*a₀^2*H₀^3*p^2/2 + a₀^2*H₀^3*p + 27*a₀*H₀^3*wₐ^3*Ω*D 0 t₀/2 - 27*a₀*H₀^3*wₐ^3*D 0 t₀/2 - 9*a₀*H₀^3*wₐ^2*p*Ω*D 0 t₀ + 9*a₀*H₀^3*wₐ^2*p*D 0 t₀ + 18*a₀*H₀^3*wₐ^2*Ω*D 0 t₀ - 18*a₀*H₀^3*wₐ^2*D 0 t₀ + 3*a₀*H₀^3*wₐ*p^2*Ω*D 0 t₀/2 - 3*a₀*H₀^3*wₐ*p^2*D 0 t₀/2 - 9*a₀*H₀^3*wₐ*p*Ω*D 0 t₀/2 + 9*a₀*H₀^3*wₐ*p*D 0 t₀/2 - 3*a₀*H₀^3*wₐ*D 0 t₀ + 27*a₀*H₀^2*wₐ^2*Ω*D 1 t₀/2 - 27*a₀*H₀^2*wₐ^2*D 1 t₀/2 - 9*a₀*H₀^2*wₐ*p*Ω*D 1 t₀/2 + 9*a₀*H₀^2*wₐ*p*D 1 t₀/2 + 27*a₀*H₀^2*wₐ*Ω*D 1 t₀/2 - 9*a₀*H₀^2*wₐ*D 1 t₀) * he_g0 - (-3*a₀^2*H₀^2*wₐ*p*Ω + 3*a₀^2*H₀^2*wₐ*p - 3*a₀^2*H₀^2*wₐ*Ω/2 + 3*a₀^2*H₀^2*wₐ/2 + a₀^2*H₀^2*p^2*Ω - a₀^2*H₀^2*p^2 - 5*a₀^2*H₀^2*p*Ω/2 + 3*a₀^2*H₀^2*p/2 - 3*a₀^2*H₀^2*Ω/2 + a₀^2*H₀^2 + 9*a₀*H₀^2*wₐ^2*Ω*D 0 t₀ - 9*a₀*H₀^2*wₐ^2*D 0 t₀ - 3*a₀*H₀^2*wₐ*p*Ω*D 0 t₀ + 3*a₀*H₀^2*wₐ*p*D 0 t₀ + 9*a₀*H₀^2*wₐ*Ω*D 0 t₀ - 6*a₀*H₀^2*wₐ*D 0 t₀ - 6*wₐ*D 1 t₀^2) * he_g1 - (2*a₀*p*G 1 t₀ + a₀*G 1 t₀ - 6*wₐ*D 0 t₀*G 1 t₀ - 9*wₐ*D 1 t₀*G 0 t₀) * he_d2 - (a₀*p*D 1 t₀ + 2*a₀*D 1 t₀ - 3*wₐ*D 0 t₀*D 1 t₀) * he_g2 - (a₀*p*G 0 t₀ - 3*wₐ*D 0 t₀*G 0 t₀) * he_d3
    have hl : (a₀^2) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have he_d4 : D 4 t₀ = a₀*H₀^4*(27*wₐ^3*Ω^2 - 108*wₐ^3*Ω + 81*wₐ^3 - 27*wₐ^2*p*Ω^2 + 108*wₐ^2*p*Ω - 81*wₐ^2*p + 63*wₐ^2*Ω^2 - 225*wₐ^2*Ω + 162*wₐ^2 + 9*wₐ*p^2*Ω^2 - 36*wₐ*p^2*Ω + 27*wₐ*p^2 - 39*wₐ*p*Ω^2 + 126*wₐ*p*Ω - 87*wₐ*p + 36*wₐ*Ω^2 - 102*wₐ*Ω + 66*wₐ - p^3*Ω^2 + 4*p^3*Ω - 3*p^3 + 6*p^2*Ω^2 - 17*p^2*Ω + 11*p^2 - 9*p*Ω^2 + 21*p*Ω - 12*p - 18*Ω + 4)/4 := by
    have h : (2*a₀^2*H₀) * (D 4 t₀ - (a₀*H₀^4*(27*wₐ^3*Ω^2 - 108*wₐ^3*Ω + 81*wₐ^3 - 27*wₐ^2*p*Ω^2 + 108*wₐ^2*p*Ω - 81*wₐ^2*p + 63*wₐ^2*Ω^2 - 225*wₐ^2*Ω + 162*wₐ^2 + 9*wₐ*p^2*Ω^2 - 36*wₐ*p^2*Ω + 27*wₐ*p^2 - 39*wₐ*p*Ω^2 + 126*wₐ*p*Ω - 87*wₐ*p + 36*wₐ*Ω^2 - 102*wₐ*Ω + 66*wₐ - p^3*Ω^2 + 4*p^3*Ω - 3*p^3 + 6*p^2*Ω^2 - 17*p^2*Ω + 11*p^2 - 9*p*Ω^2 + 21*p*Ω - 12*p - 18*Ω + 4)/4)) = 0 := by
      linear_combination z0_3 - (-27*a₀^2*H₀^5*wₐ^3*Ω^2/2 + 54*a₀^2*H₀^5*wₐ^3*Ω - 81*a₀^2*H₀^5*wₐ^3/2 + 27*a₀^2*H₀^5*wₐ^2*p*Ω^2/2 - 54*a₀^2*H₀^5*wₐ^2*p*Ω + 81*a₀^2*H₀^5*wₐ^2*p/2 - 117*a₀^2*H₀^5*wₐ^2*Ω^2/2 + 198*a₀^2*H₀^5*wₐ^2*Ω - 279*a₀^2*H₀^5*wₐ^2/2 - 9*a₀^2*H₀^5*wₐ*p^2*Ω^2/2 + 18*a₀^2*H₀^5*wₐ*p^2*Ω - 27*a₀^2*H₀^5*wₐ*p^2/2 + 75*a₀^2*H₀^5*wₐ*p*Ω^2/2 - 120*a₀^2*H₀^5*wₐ*p*Ω + 165*a₀^2*H₀^5*wₐ*p/2 - 72*a₀^2*H₀^5*wₐ*Ω^2 + 183*a₀^2*H₀^5*wₐ*Ω - 111*a₀^2*H₀^5*wₐ + a₀^2*H₀^5*p^3*Ω^2/2 - 2*a₀^2*H₀^5*p^3*Ω + 3*a₀^2*H₀^5*p^3/2 - 6*a₀^2*H₀^5*p^2*Ω^2 + 18*a₀^2*H₀^5*p^2*Ω - 12*a₀^2*H₀^5*p^2 + 45*a₀^2*H₀^5*p*Ω^2/2 - 51*a₀^2*H₀^5*p*Ω + 57*a₀^2*H₀^5*p/2 - 27*a₀^2*H₀^5*Ω^2 + 39*a₀^2*H₀^5*Ω - 15*a₀^2*H₀^5 - 54*a₀*H₀^5*wₐ^3*Ω^2*D 0 t₀ + 135*a₀*H₀^5*wₐ^3*Ω*D 0 t₀ - 81*a₀*H₀^5*wₐ^3*D 0 t₀ + 54*a₀*H₀^5*wₐ^2*p*Ω^2*D 0 t₀ - 135*a₀*H₀^5*wₐ^2*p*Ω*D 0 t₀ + 81*a₀*H₀^5*wₐ^2*p*D 0 t₀ - 153*a₀*H₀^5*wₐ^2*Ω^2*D 0 t₀ + 747*a₀*H₀^5*wₐ^2*Ω*D 0 t₀/2 - 441*a₀*H₀^5*wₐ^2*D 0 t₀/2 - 18*a₀*H₀^5*wₐ*p^2*Ω^2*D 0 t₀ + 45*a₀*H₀^5*wₐ*p^2*Ω*D 0 t₀ - 27*a₀*H₀^5*wₐ*p^2*D 0 t₀ + 96*a₀*H₀^5*wₐ*p*Ω^2*D 0 t₀ - 228*a₀*H₀^5*wₐ*p*Ω*D 0 t₀ + 132*a₀*H₀^5*wₐ*p*D 0 t₀ - 99*a₀*H₀^5*wₐ*Ω^2*D 0 t₀ + 174*a₀*H₀^5*wₐ*Ω*D 0 t₀ - 75*a₀*H₀^5*wₐ*D 0 t₀ + 2*a₀*H₀^5*p^3*Ω^2*D 0 t₀ - 5*a₀*H₀^5*p^3*Ω*D 0 t₀ + 3*a₀*H₀^5*p^3*D 0 t₀ - 15*a₀*H₀^5*p^2*Ω^2*D 0 t₀ + 69*a₀*H₀^5*p^2*Ω*D 0 t₀/2 - 39*a₀*H₀^5*p^2*D 0 t₀/2 + 27*a₀*H₀^5*p*Ω^2*D 0 t₀ - 81*a₀*H₀^5*p*Ω*D 0 t₀/2 + 27*a₀*H₀^5*p*D 0 t₀/2 + 3*a₀*H₀^5*Ω*D 0 t₀ - 3*a₀*H₀^5*D 0 t₀ + 2*a₀*H₀*D 4 t₀ - 54*H₀^5*wₐ^3*Ω^2*D 0 t₀^2 + 135*H₀^5*wₐ^3*Ω*D 0 t₀^2 - 81*H₀^5*wₐ^3*D 0 t₀^2 + 54*H₀^5*wₐ^2*p*Ω^2*D 0 t₀^2 - 135*H₀^5*wₐ^2*p*Ω*D 0 t₀^2 + 81*H₀^5*wₐ^2*p*D 0 t₀^2 - 117*H₀^5*wₐ^2*Ω^2*D 0 t₀^2/2 + 207*H₀^5*wₐ^2*Ω*D 0 t₀^2/2 - 45*H₀^5*wₐ^2*D 0 t₀^2 - 18*H₀^5*wₐ*p^2*Ω^2*D 0 t₀^2 + 45*H₀^5*wₐ*p^2*Ω*D 0 t₀^2 - 27*H₀^5*wₐ*p^2*D 0 t₀^2 + 33*H₀^5*wₐ*p*Ω^2*D 0 t₀^2 - 48*H₀^5*wₐ*p*Ω*D 0 t₀^2 + 15*H₀^5*wₐ*p*D 0 t₀^2 + 3*H₀^5*wₐ*Ω*D 0 t₀^2 - 3*H₀^5*wₐ*D 0 t₀^2 + 2*H₀^5*p^3*Ω^2*D 0 t₀^2 - 5*H₀^5*p^3*Ω*D 0 t₀^2 + 3*H₀^5*p^3*D 0 t₀^2 - 9*H₀^5*p^2*Ω^2*D 0 t₀^2/2 + 9*H₀^5*p^2*Ω*D 0 t₀^2/2 - 9*H₀^5*p*Ω^2*D 0 t₀^2/2 + 9*H₀^5*p*Ω*D 0 t₀^2/2) * he_d0 - (27*a₀^2*H₀^4*wₐ^2*Ω^2 - 171*a₀^2*H₀^4*wₐ^2*Ω/2 + 117*a₀^2*H₀^4*wₐ^2/2 - 18*a₀^2*H₀^4*wₐ*p*Ω^2 + 57*a₀^2*H₀^4*wₐ*p*Ω - 39*a₀^2*H₀^4*wₐ*p + 54*a₀^2*H₀^4*wₐ*Ω^2 - 132*a₀^2*H₀^4*wₐ*Ω + 78*a₀^2*H₀^4*wₐ + 3*a₀^2*H₀^4*p^2*Ω^2 - 19*a₀^2*H₀^4*p^2*Ω/2 + 13*a₀^2*H₀^4*p^2/2 - 18*a₀^2*H₀^4*p*Ω^2 + 81*a₀^2*H₀^4*p*Ω/2 - 45*a₀^2*H₀^4*p/2 + 27*a₀^2*H₀^4*Ω^2 - 30*a₀^2*H₀^4*Ω + 13*a₀^2*H₀^4 - 27*a₀*H₀^4*wₐ*Ω^2*D 0 t₀ + 108*a₀*H₀^4*wₐ*Ω*D 0 t₀ - 81*a₀*H₀^4*wₐ*D 0 t₀ + 9*a₀*H₀^4*p*Ω^2*D 0 t₀ - 36*a₀*H₀^4*p*Ω*D 0 t₀ + 27*a₀*H₀^4*p*D 0 t₀ - 27*a₀*H₀^4*Ω^2*D 0 t₀ + 45*a₀*H₀^4*Ω*D 0 t₀ - 18*a₀*H₀^4*D 0 t₀ - 63*a₀*H₀^3*wₐ^2*Ω*D 1 t₀/2 + 63*a₀*H₀^3*wₐ^2*D 1 t₀/2 + 21*a₀*H₀^3*wₐ*p*Ω*D 1 t₀ - 21*a₀*H₀^3*wₐ*p*D 1 t₀ - 42*a₀*H₀^3*wₐ*Ω*D 1 t₀ + 42*a₀*H₀^3*wₐ*D 1 t₀ - 7*a₀*H₀^3*p^2*Ω*D 1 t₀/2 + 7*a₀*H₀^3*p^2*D 1 t₀/2 + 21*a₀*H₀^3*p*Ω*D 1 t₀/2 - 21*a₀*H₀^3*p*D 1 t₀/2 + 6*a₀*H₀^3*Ω*D 1 t₀ + a₀*H₀^3*D 1 t₀ - 81*H₀^4*wₐ^2*Ω^2*D 0 t₀^2/2 + 162*H₀^4*wₐ^2*Ω*D 0 t₀^2 - 243*H₀^4*wₐ^2*D 0 t₀^2/2 + 27*H₀^4*wₐ*p*Ω^2*D 0 t₀^2 - 108*H₀^4*wₐ*p*Ω*D 0 t₀^2 + 81*H₀^4*wₐ*p*D 0 t₀^2 - 81*H₀^4*wₐ*Ω^2*D 0 t₀^2/2 + 135*H₀^4*wₐ*Ω*D 0 t₀^2/2 - 27*H₀^4*wₐ*D 0 t₀^2 - 9*H₀^4*p^2*Ω^2*D 0 t₀^2/2 + 18*H₀^4*p^2*Ω*D 0 t₀^2 - 27*H₀^4*p^2*D 0 t₀^2/2 + 27*H₀^4*p*Ω^2*D 0 t₀^2/2 - 27*H₀^4*p*Ω*D 0 t₀^2/2 + 54*H₀^3*wₐ*Ω*D 0 t₀*D 1 t₀ - 54*H₀^3*wₐ*D 0 t₀*D 1 t₀ - 18*H₀^3*p*Ω*D 0 t₀*D 1 t₀ + 18*H₀^3*p*D 0 t₀*D 1 t₀ + 6*H₀^2*Ω*D 1 t₀^2 - 6*H₀^2*D 1 t₀^2 + 2*D 0 t₀*D 4 t₀) * he_d1 - (-27*a₀*H₀^5*wₐ^2*Ω^2*D 0 t₀^2/2 + 27*a₀*H₀^5*wₐ^2*Ω*D 0 t₀^2 - 27*a₀*H₀^5*wₐ^2*D 0 t₀^2/2 + 9*a₀*H₀^5*wₐ*p*Ω^2*D 0 t₀^2 - 18*a₀*H₀^5*wₐ*p*Ω*D 0 t₀^2 + 9*a₀*H₀^5*wₐ*p*D 0 t₀^2 - 18*a₀*H₀^5*wₐ*Ω^2*D 0 t₀^2 + 36*a₀*H₀^5*wₐ*Ω*D 0 t₀^2 - 18*a₀*H₀^5*wₐ*D 0 t₀^2 - 3*a₀*H₀^5*p^2*Ω^2*D 0 t₀^2/2 + 3*a₀*H₀^5*p^2*Ω*D 0 t₀^2 - 3*a₀*H₀^5*p^2*D 0 t₀^2/2 + 9*a₀*H₀^5*p*Ω^2*D 0 t₀^2/2 - 9*a₀*H₀^5*p*Ω*D 0 t₀^2 + 9*a₀*H₀^5*p*D 0 t₀^2/2 + 3*a₀*H₀^5*Ω*D 0 t₀^2 - 3*a₀*H₀^5*D 0 t₀^2 - 27*a₀*H₀^4*wₐ*Ω^2*D 0 t₀*D 1 t₀ + 54*a₀*H₀^4*wₐ*Ω*D 0 t₀*D 1 t₀ - 27*a₀*H₀^4*wₐ*D 0 t₀*D 1 t₀ + 9*a₀*H₀^4*p*Ω^2*D 0 t₀*D 1 t₀ - 18*a₀*H₀^4*p*Ω*D 0 t₀*D 1 t₀ + 9*a₀*H₀^4*p*D 0 t₀*D 1 t₀ - 27*a₀*H₀^4*Ω^2*D 0 t₀*D 1 t₀ + 45*a₀*H₀^4*Ω*D 0 t₀*D 1 t₀ - 18*a₀*H₀^4*D 0 t₀*D 1 t₀ + 6*H₀^2*Ω*D 1 t₀^3 - 6*H₀^2*D 1 t₀^3) * he_g0 - (-27*a₀*H₀^4*wₐ*Ω^2*D 0 t₀^2/2 + 27*a₀*H₀^4*wₐ*Ω*D 0 t₀^2 - 27*a₀*H₀^4*wₐ*D 0 t₀^2/2 + 9*a₀*H₀^4*p*Ω^2*D 0 t₀^2/2 - 9*a₀*H₀^4*p*Ω*D 0 t₀^2 + 9*a₀*H₀^4*p*D 0 t₀^2/2 - 27*a₀*H₀^4*Ω^2*D 0 t₀^2/2 + 45*a₀*H₀^4*Ω*D 0 t₀^2/2 - 9*a₀*H₀^4*D 0 t₀^2 + 18*H₀^2*Ω*D 0 t₀*D 1 t₀^2 - 18*H₀^2*D 0 t₀*D 1 t₀^2) * he_g1 - (-27*a₀*H₀^3*wₐ^2*Ω*D 0 t₀ + 27*a₀*H₀^3*wₐ^2*D 0 t₀ + 18*a₀*H₀^3*wₐ*p*Ω*D 0 t₀ - 18*a₀*H₀^3*wₐ*p*D 0 t₀ - 36*a₀*H₀^3*wₐ*Ω*D 0 t₀ + 36*a₀*H₀^3*wₐ*D 0 t₀ - 3*a₀*H₀^3*p^2*Ω*D 0 t₀ + 3*a₀*H₀^3*p^2*D 0 t₀ + 9*a₀*H₀^3*p*Ω*D 0 t₀ - 9*a₀*H₀^3*p*D 0 t₀ + 6*a₀*H₀^3*D 0 t₀ - 18*a₀*H₀^2*wₐ*Ω*D 1 t₀ + 18*a₀*H₀^2*wₐ*D 1 t₀ + 6*a₀*H₀^2*p*Ω*D 1 t₀ - 6*a₀*H₀^2*p*D 1 t₀ - 18*a₀*H₀^2*Ω*D 1 t₀ + 12*a₀*H₀^2*D 1 t₀ + 9*H₀^2*Ω*D 0 t₀^2*G 1 t₀ + 18*H₀^2*Ω*D 0 t₀*D 1 t₀*G 0 t₀ - 9*H₀^2*D 0 t₀^2*G 1 t₀ - 18*H₀^2*D 0 t₀*D 1 t₀*G 0 t₀ + 12*D 1 t₀*D 2 t₀) * he_d2 - (9*H₀^2*Ω*D 0 t₀^2*D 1 t₀ - 9*H₀^2*D 0 t₀^2*D 1 t₀) * he_g2 - (3*H₀^2*Ω*D 0 t₀^2*G 0 t₀ - 3*H₀^2*D 0 t₀^2*G 0 t₀ + 6*D 0 t₀*D 2 t₀ + 7*D 1 t₀^2) * he_d3 - (H₀^2*Ω*D 0 t₀^3 - H₀^2*D 0 t₀^3) * he_g3
    have hl : (2*a₀^2*H₀) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have he_g4 : G 4 t₀ = H₀^4*(324*wₐ^4*Ω^2 - 2430*wₐ^4*Ω + 2430*wₐ^4 - 432*wₐ^3*p*Ω^2 + 3240*wₐ^3*p*Ω - 3240*wₐ^3*p + 675*wₐ^3*Ω^2 - 3321*wₐ^3*Ω + 2322*wₐ^3 + 216*wₐ^2*p^2*Ω^2 - 1620*wₐ^2*p^2*Ω + 1620*wₐ^2*p^2 - 639*wₐ^2*p*Ω^2 + 2727*wₐ^2*p*Ω - 1548*wₐ^2*p + 351*wₐ^2*Ω^2 - 630*wₐ^2*Ω + 450*wₐ^2 - 48*wₐ*p^3*Ω^2 + 360*wₐ*p^3*Ω - 360*wₐ*p^3 + 201*wₐ*p^2*Ω^2 - 711*wₐ*p^2*Ω + 258*wₐ*p^2 - 171*wₐ*p*Ω^2 - 57*wₐ*p*Ω - 90*wₐ*p - 54*wₐ*Ω + 12*wₐ + 4*p^4*Ω^2 - 30*p^4*Ω + 30*p^4 - 21*p^3*Ω^2 + 57*p^3*Ω + 18*p^2*Ω^2 + 81*p^2*Ω + 27*p*Ω^2 + 54*p*Ω)/4 := by
    have h : (a₀^2) * (G 4 t₀ - (H₀^4*(324*wₐ^4*Ω^2 - 2430*wₐ^4*Ω + 2430*wₐ^4 - 432*wₐ^3*p*Ω^2 + 3240*wₐ^3*p*Ω - 3240*wₐ^3*p + 675*wₐ^3*Ω^2 - 3321*wₐ^3*Ω + 2322*wₐ^3 + 216*wₐ^2*p^2*Ω^2 - 1620*wₐ^2*p^2*Ω + 1620*wₐ^2*p^2 - 639*wₐ^2*p*Ω^2 + 2727*wₐ^2*p*Ω - 1548*wₐ^2*p + 351*wₐ^2*Ω^2 - 630*wₐ^2*Ω + 450*wₐ^2 - 48*wₐ*p^3*Ω^2 + 360*wₐ*p^3*Ω - 360*wₐ*p^3 + 201*wₐ*p^2*Ω^2 - 711*wₐ*p^2*Ω + 258*wₐ*p^2 - 171*wₐ*p*Ω^2 - 57*wₐ*p*Ω - 90*wₐ*p - 54*wₐ*Ω + 12*wₐ + 4*p^4*Ω^2 - 30*p^4*Ω + 30*p^4 - 21*p^3*Ω^2 + 57*p^3*Ω + 18*p^2*Ω^2 + 81*p^2*Ω + 27*p*Ω^2 + 54*p*Ω)/4)) = 0 := by
      linear_combination z1_3 - (-81*a₀*H₀^4*wₐ^4*Ω^2 + 1215*a₀*H₀^4*wₐ^4*Ω/2 - 1215*a₀*H₀^4*wₐ^4/2 + 81*a₀*H₀^4*wₐ^3*p*Ω^2 - 1215*a₀*H₀^4*wₐ^3*p*Ω/2 + 1215*a₀*H₀^4*wₐ^3*p/2 - 675*a₀*H₀^4*wₐ^3*Ω^2/4 + 3321*a₀*H₀^4*wₐ^3*Ω/4 - 1161*a₀*H₀^4*wₐ^3/2 - 27*a₀*H₀^4*wₐ^2*p^2*Ω^2 + 405*a₀*H₀^4*wₐ^2*p^2*Ω/2 - 405*a₀*H₀^4*wₐ^2*p^2/2 + 441*a₀*H₀^4*wₐ^2*p*Ω^2/4 - 981*a₀*H₀^4*wₐ^2*p*Ω/2 + 1197*a₀*H₀^4*wₐ^2*p/4 - 351*a₀*H₀^4*wₐ^2*Ω^2/4 + 315*a₀*H₀^4*wₐ^2*Ω/2 - 225*a₀*H₀^4*wₐ^2/2 + 3*a₀*H₀^4*wₐ*p^3*Ω^2 - 45*a₀*H₀^4*wₐ*p^3*Ω/2 + 45*a₀*H₀^4*wₐ*p^3/2 - 18*a₀*H₀^4*wₐ*p^2*Ω^2 + 285*a₀*H₀^4*wₐ*p^2*Ω/4 - 141*a₀*H₀^4*wₐ*p^2/4 + 27*a₀*H₀^4*wₐ*p*Ω^2 - 63*a₀*H₀^4*wₐ*p*Ω/4 + 18*a₀*H₀^4*wₐ*p + 27*a₀*H₀^4*wₐ*Ω/2 - 3*a₀*H₀^4*wₐ + a₀*G 4 t₀) * he_d0 - (-54*a₀*H₀^3*wₐ^3*p*Ω + 81*a₀*H₀^3*wₐ^3*p + 54*a₀*H₀^3*wₐ^3*Ω - 54*a₀*H₀^3*wₐ^3 + 54*a₀*H₀^3*wₐ^2*p^2*Ω - 81*a₀*H₀^3*wₐ^2*p^2 - 81*a₀*H₀^3*wₐ^2*p*Ω/2 + 117*a₀*H₀^3*wₐ^2*Ω/2 - 45*a₀*H₀^3*wₐ^2 - 18*a₀*H₀^3*wₐ*p^3*Ω + 27*a₀*H₀^3*wₐ*p^3 + 3*a₀*H₀^3*wₐ*p^2*Ω + 33*a₀*H₀^3*wₐ*p^2 + 27*a₀*H₀^3*wₐ*p*Ω + 3*a₀*H₀^3*wₐ*p - 3*a₀*H₀^3*wₐ + 2*a₀*H₀^3*p^4*Ω - 3*a₀*H₀^3*p^4 + 3*a₀*H₀^3*p^3*Ω/2 - 9*a₀*H₀^3*p^3 - 18*a₀*H₀^3*p^2*Ω - 27*a₀*H₀^3*p*Ω/2 + 162*H₀^3*wₐ^4*Ω*D 0 t₀ - 243*H₀^3*wₐ^4*D 0 t₀ - 162*H₀^3*wₐ^3*p*Ω*D 0 t₀ + 243*H₀^3*wₐ^3*p*D 0 t₀ + 351*H₀^3*wₐ^3*Ω*D 0 t₀/2 - 135*H₀^3*wₐ^3*D 0 t₀ + 54*H₀^3*wₐ^2*p^2*Ω*D 0 t₀ - 81*H₀^3*wₐ^2*p^2*D 0 t₀ - 99*H₀^3*wₐ^2*p*Ω*D 0 t₀ + 45*H₀^3*wₐ^2*p*D 0 t₀ - 9*H₀^3*wₐ^2*D 0 t₀ - 6*H₀^3*wₐ*p^3*Ω*D 0 t₀ + 9*H₀^3*wₐ*p^3*D 0 t₀ + 27*H₀^3*wₐ*p^2*Ω*D 0 t₀/2 + 27*H₀^3*wₐ*p*Ω*D 0 t₀/2 + 81*H₀^2*wₐ^3*Ω*D 1 t₀/2 - 243*H₀^2*wₐ^3*D 1 t₀/2 - 27*H₀^2*wₐ^2*p*Ω*D 1 t₀ + 81*H₀^2*wₐ^2*p*D 1 t₀ + 81*H₀^2*wₐ^2*Ω*D 1 t₀/2 - 27*H₀^2*wₐ^2*D 1 t₀ + 9*H₀^2*wₐ*p^2*Ω*D 1 t₀/2 - 27*H₀^2*wₐ*p^2*D 1 t₀/2 - 27*H₀^2*wₐ*p*Ω*D 1 t₀/2) * he_d1 - (27*a₀^2*H₀^4*wₐ^3*p*Ω^2/4 - 27*a₀^2*H₀^4*wₐ^3*p*Ω + 81*a₀^2*H₀^4*wₐ^3*p/4 - 81*a₀^2*H₀^4*wₐ^3*Ω^2/4 + 81*a₀^2*H₀^4*wₐ^3*Ω/2 - 81*a₀^2*H₀^4*wₐ^3/4 - 27*a₀^2*H₀^4*wₐ^2*p^2*Ω^2/4 + 27*a₀^2*H₀^4*wₐ^2*p^2*Ω - 81*a₀^2*H₀^4*wₐ^2*p^2/4 + 117*a₀^2*H₀^4*wₐ^2*p*Ω^2/4 - 333*a₀^2*H₀^4*wₐ^2*p*Ω/4 + 54*a₀^2*H₀^4*wₐ^2*p - 81*a₀^2*H₀^4*wₐ^2*Ω^2/2 + 135*a₀^2*H₀^4*wₐ^2*Ω/2 - 27*a₀^2*H₀^4*wₐ^2 + 9*a₀^2*H₀^4*wₐ*p^3*Ω^2/4 - 9*a₀^2*H₀^4*wₐ*p^3*Ω + 27*a₀^2*H₀^4*wₐ*p^3/4 - 12*a₀^2*H₀^4*wₐ*p^2*Ω^2 + 36*a₀^2*H₀^4*wₐ*p^2*Ω - 24*a₀^2*H₀^4*wₐ*p^2 + 45*a₀^2*H₀^4*wₐ*p*Ω^2/2 - 48*a₀^2*H₀^4*wₐ*p*Ω + 51*a₀^2*H₀^4*wₐ*p/2 - 81*a₀^2*H₀^4*wₐ*Ω^2/4 + 27*a₀^2*H₀^4*wₐ*Ω - 9*a₀^2*H₀^4*wₐ - a₀^2*H₀^4*p^4*Ω^2/4 + a₀^2*H₀^4*p^4*Ω - 3*a₀^2*H₀^4*p^4/4 + 3*a₀^2*H₀^4*p^3*Ω^2/2 - 17*a₀^2*H₀^4*p^3*Ω/4 + 11*a₀^2*H₀^4*p^3/4 - 9*a₀^2*H₀^4*p^2*Ω^2/4 + 21*a₀^2*H₀^4*p^2*Ω/4 - 3*a₀^2*H₀^4*p^2 - 9*a₀^2*H₀^4*p*Ω/2 + a₀^2*H₀^4*p - 81*a₀*H₀^4*wₐ^4*Ω^2*D 0 t₀/4 + 81*a₀*H₀^4*wₐ^4*Ω*D 0 t₀ - 243*a₀*H₀^4*wₐ^4*D 0 t₀/4 + 81*a₀*H₀^4*wₐ^3*p*Ω^2*D 0 t₀/4 - 81*a₀*H₀^4*wₐ^3*p*Ω*D 0 t₀ + 243*a₀*H₀^4*wₐ^3*p*D 0 t₀/4 - 189*a₀*H₀^4*wₐ^3*Ω^2*D 0 t₀/4 + 675*a₀*H₀^4*wₐ^3*Ω*D 0 t₀/4 - 243*a₀*H₀^4*wₐ^3*D 0 t₀/2 - 27*a₀*H₀^4*wₐ^2*p^2*Ω^2*D 0 t₀/4 + 27*a₀*H₀^4*wₐ^2*p^2*Ω*D 0 t₀ - 81*a₀*H₀^4*wₐ^2*p^2*D 0 t₀/4 + 117*a₀*H₀^4*wₐ^2*p*Ω^2*D 0 t₀/4 - 189*a₀*H₀^4*wₐ^2*p*Ω*D 0 t₀/2 + 261*a₀*H₀^4*wₐ^2*p*D 0 t₀/4 - 27*a₀*H₀^4*wₐ^2*Ω^2*D 0 t₀ + 153*a₀*H₀^4*wₐ^2*Ω*D 0 t₀/2 - 99*a₀*H₀^4*wₐ^2*D 0 t₀/2 + 3*a₀*H₀^4*wₐ*p^3*Ω^2*D 0 t₀/4 - 3*a₀*H₀^4*wₐ*p^3*Ω*D 0 t₀ + 9*a₀*H₀^4*wₐ*p^3*D 0 t₀/4 - 9*a₀*H₀^4*wₐ*p^2*Ω^2*D 0 t₀/2 + 51*a₀*H₀^4*wₐ*p^2*Ω*D 0 t₀/4 - 33*a₀*H₀^4*wₐ*p^2*D 0 t₀/4 + 27*a₀*H₀^4*wₐ*p*Ω^2*D 0 t₀/4 - 63*a₀*H₀^4*wₐ*p*Ω*D 0 t₀/4 + 9*a₀*H₀^4*wₐ*p*D 0 t₀ + 27*a₀*H₀^4*wₐ*Ω*D 0 t₀/2 - 3*a₀*H₀^4*wₐ*D 0 t₀ + 54*a₀*H₀^3*wₐ^3*Ω*D 1 t₀ - 54*a₀*H₀^3*wₐ^3*D 1 t₀ - 36*a₀*H₀^3*wₐ^2*p*Ω*D 1 t₀ + 36*a₀*H₀^3*wₐ^2*p*D 1 t₀ + 72*a₀*H₀^3*wₐ^2*Ω*D 1 t₀ - 72*a₀*H₀^3*wₐ^2*D 1 t₀ + 6*a₀*H₀^3*wₐ*p^2*Ω*D 1 t₀ - 6*a₀*H₀^3*wₐ*p^2*D 1 t₀ - 18*a₀*H₀^3*wₐ*p*Ω*D 1 t₀ + 18*a₀*H₀^3*wₐ*p*D 1 t₀ - 12*a₀*H₀^3*wₐ*D 1 t₀) * he_g0 - (-27*a₀^2*H₀^3*wₐ^2*p*Ω/2 + 27*a₀^2*H₀^3*wₐ^2*p/2 - 9*a₀^2*H₀^3*wₐ^2*Ω/2 + 9*a₀^2*H₀^3*wₐ^2/2 + 9*a₀^2*H₀^3*wₐ*p^2*Ω - 9*a₀^2*H₀^3*wₐ*p^2 - 15*a₀^2*H₀^3*wₐ*p*Ω + 15*a₀^2*H₀^3*wₐ*p - 6*a₀^2*H₀^3*wₐ*Ω + 6*a₀^2*H₀^3*wₐ - 3*a₀^2*H₀^3*p^3*Ω/2 + 3*a₀^2*H₀^3*p^3/2 + 4*a₀^2*H₀^3*p^2*Ω - 4*a₀^2*H₀^3*p^2 + 3*a₀^2*H₀^3*p*Ω/2 + 3*a₀^2*H₀^3*p/2 + a₀^2*H₀^3 + 81*a₀*H₀^3*wₐ^3*Ω*D 0 t₀/2 - 81*a₀*H₀^3*wₐ^3*D 0 t₀/2 - 27*a₀*H₀^3*wₐ^2*p*Ω*D 0 t₀ + 27*a₀*H₀^3*wₐ^2*p*D 0 t₀ + 54*a₀*H₀^3*wₐ^2*Ω*D 0 t₀ - 54*a₀*H₀^3*wₐ^2*D 0 t₀ + 9*a₀*H₀^3*wₐ*p^2*Ω*D 0 t₀/2 - 9*a₀*H₀^3*wₐ*p^2*D 0 t₀/2 - 27*a₀*H₀^3*wₐ*p*Ω*D 0 t₀/2 + 27*a₀*H₀^3*wₐ*p*D 0 t₀/2 - 9*a₀*H₀^3*wₐ*D 0 t₀ + 81*a₀*H₀^2*wₐ^2*Ω*D 1 t₀/2 - 81*a₀*H₀^2*wₐ^2*D 1 t₀/2 - 27*a₀*H₀^2*wₐ*p*Ω*D 1 t₀/2 + 27*a₀*H₀^2*wₐ*p*D 1 t₀/2 + 81*a₀*H₀^2*wₐ*Ω*D 1 t₀/2 - 27*a₀*H₀^2*wₐ*D 1 t₀) * he_g1 - (-27*a₀*H₀^2*wₐ^2*p*Ω/2 + 81*a₀*H₀^2*wₐ^2*p/2 + 27*a₀*H₀^2*wₐ^2*Ω*G 0 t₀/2 - 27*a₀*H₀^2*wₐ^2*Ω/2 - 27*a₀*H₀^2*wₐ^2*G 0 t₀/2 + 81*a₀*H₀^2*wₐ^2/2 + 9*a₀*H₀^2*wₐ*p^2*Ω - 27*a₀*H₀^2*wₐ*p^2 - 9*a₀*H₀^2*wₐ*p*Ω*G 0 t₀/2 - 9*a₀*H₀^2*wₐ*p*Ω/2 + 9*a₀*H₀^2*wₐ*p*G 0 t₀/2 - 18*a₀*H₀^2*wₐ*p + 27*a₀*H₀^2*wₐ*Ω*G 0 t₀/2 - 27*a₀*H₀^2*wₐ*Ω/2 - 9*a₀*H₀^2*wₐ*G 0 t₀ + 9*a₀*H₀^2*wₐ - 3*a₀*H₀^2*p^3*Ω/2 + 9*a₀*H₀^2*p^3/2 + 3*a₀*H₀^2*p^2*Ω + 9*a₀*H₀^2*p^2/2 + 9*a₀*H₀^2*p*Ω/2 + 81*H₀^2*wₐ^3*Ω*D 0 t₀/2 - 243*H₀^2*wₐ^3*D 0 t₀/2 - 27*H₀^2*wₐ^2*p*Ω*D 0 t₀ + 81*H₀^2*wₐ^2*p*D 0 t₀ + 81*H₀^2*wₐ^2*Ω*D 0 t₀/2 - 27*H₀^2*wₐ^2*D 0 t₀ + 9*H₀^2*wₐ*p^2*Ω*D 0 t₀/2 - 27*H₀^2*wₐ*p^2*D 0 t₀/2 - 27*H₀^2*wₐ*p*Ω*D 0 t₀/2 - 27*wₐ*D 1 t₀*G 1 t₀ - 9*wₐ*D 2 t₀*G 0 t₀) * he_d2 - (3*a₀*p*D 2 t₀ + 3*a₀*D 2 t₀ - 9*wₐ*D 0 t₀*D 2 t₀ - 9*wₐ*D 1 t₀^2) * he_g2 - (3*a₀*p*G 1 t₀ + a₀*G 1 t₀ - 9*wₐ*D 0 t₀*G 1 t₀ - 12*wₐ*D 1 t₀*G 0 t₀) * he_d3 - (a₀*p*D 1 t₀ + 3*a₀*D 1 t₀ - 3*wₐ*D 0 t₀*D 1 t₀) * he_g3 - (a₀*p*G 0 t₀ - 3*wₐ*D 0 t₀*G 0 t₀) * he_d4
    have hl : (a₀^2) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have he_d5 : D 5 t₀ = a₀*H₀^5*(324*wₐ^4*Ω^2 - 810*wₐ^4*Ω + 486*wₐ^4 - 432*wₐ^3*p*Ω^2 + 1080*wₐ^3*p*Ω - 648*wₐ^3*p + 945*wₐ^3*Ω^2 - 2241*wₐ^3*Ω + 1296*wₐ^3 + 216*wₐ^2*p^2*Ω^2 - 540*wₐ^2*p^2*Ω + 324*wₐ^2*p^2 - 846*wₐ^2*p*Ω^2 + 1935*wₐ^2*p*Ω - 1089*wₐ^2*p + 792*wₐ^2*Ω^2 - 1674*wₐ^2*Ω + 882*wₐ^2 - 48*wₐ*p^3*Ω^2 + 120*wₐ*p^3*Ω - 72*wₐ*p^3 + 249*wₐ*p^2*Ω^2 - 543*wₐ*p^2*Ω + 294*wₐ*p^2 - 387*wₐ*p*Ω^2 + 765*wₐ*p*Ω - 378*wₐ*p + 216*wₐ*Ω^2 - 372*wₐ*Ω + 156*wₐ + 4*p^4*Ω^2 - 10*p^4*Ω + 6*p^4 - 24*p^3*Ω^2 + 49*p^3*Ω - 25*p^3 + 42*p^2*Ω^2 - 77*p^2*Ω + 35*p^2 - 36*p*Ω^2 + 56*p*Ω - 20*p + 54*Ω^2 + 12*Ω + 4)/4 := by
    have h : (2*a₀^2*H₀) * (D 5 t₀ - (a₀*H₀^5*(324*wₐ^4*Ω^2 - 810*wₐ^4*Ω + 486*wₐ^4 - 432*wₐ^3*p*Ω^2 + 1080*wₐ^3*p*Ω - 648*wₐ^3*p + 945*wₐ^3*Ω^2 - 2241*wₐ^3*Ω + 1296*wₐ^3 + 216*wₐ^2*p^2*Ω^2 - 540*wₐ^2*p^2*Ω + 324*wₐ^2*p^2 - 846*wₐ^2*p*Ω^2 + 1935*wₐ^2*p*Ω - 1089*wₐ^2*p + 792*wₐ^2*Ω^2 - 1674*wₐ^2*Ω + 882*wₐ^2 - 48*wₐ*p^3*Ω^2 + 120*wₐ*p^3*Ω - 72*wₐ*p^3 + 249*wₐ*p^2*Ω^2 - 543*wₐ*p^2*Ω + 294*wₐ*p^2 - 387*wₐ*p*Ω^2 + 765*wₐ*p*Ω - 378*wₐ*p + 216*wₐ*Ω^2 - 372*wₐ*Ω + 156*wₐ + 4*p^4*Ω^2 - 10*p^4*Ω + 6*p^4 - 24*p^3*Ω^2 + 49*p^3*Ω - 25*p^3 + 42*p^2*Ω^2 - 77*p^2*Ω + 35*p^2 - 36*p*Ω^2 + 56*p*Ω - 20*p + 54*Ω^2 + 12*Ω + 4)/4)) = 0 := by
      linear_combination z0_4 - (-162*a₀^2*H₀^6*wₐ^4*Ω^2 + 405*a₀^2*H₀^6*wₐ^4*Ω - 243*a₀^2*H₀^6*wₐ^4 + 216*a₀^2*H₀^6*wₐ^3*p*Ω^2 - 540*a₀^2*H₀^6*wₐ^3*p*Ω + 324*a₀^2*H₀^6*wₐ^3*p + 81*a₀^2*H₀^6*wₐ^3*Ω^3/2 - 3807*a₀^2*H₀^6*wₐ^3*Ω^2/4 + 2079*a₀^2*H₀^6*wₐ^3*Ω - 4671*a₀^2*H₀^6*wₐ^3/4 - 108*a₀^2*H₀^6*wₐ^2*p^2*Ω^2 + 270*a₀^2*H₀^6*wₐ^2*p^2*Ω - 162*a₀^2*H₀^6*wₐ^2*p^2 - 81*a₀^2*H₀^6*wₐ^2*p*Ω^3/2 + 3609*a₀^2*H₀^6*wₐ^2*p*Ω^2/4 - 1926*a₀^2*H₀^6*wₐ^2*p*Ω + 4257*a₀^2*H₀^6*wₐ^2*p/4 + 243*a₀^2*H₀^6*wₐ^2*Ω^3/2 - 6219*a₀^2*H₀^6*wₐ^2*Ω^2/4 + 11655*a₀^2*H₀^6*wₐ^2*Ω/4 - 2961*a₀^2*H₀^6*wₐ^2/2 + 24*a₀^2*H₀^6*wₐ*p^3*Ω^2 - 60*a₀^2*H₀^6*wₐ*p^3*Ω + 36*a₀^2*H₀^6*wₐ*p^3 + 27*a₀^2*H₀^6*wₐ*p^2*Ω^3/2 - 1137*a₀^2*H₀^6*wₐ*p^2*Ω^2/4 + 591*a₀^2*H₀^6*wₐ*p^2*Ω - 1281*a₀^2*H₀^6*wₐ*p^2/4 - 81*a₀^2*H₀^6*wₐ*p*Ω^3 + 3705*a₀^2*H₀^6*wₐ*p*Ω^2/4 - 1647*a₀^2*H₀^6*wₐ*p*Ω + 3207*a₀^2*H₀^6*wₐ*p/4 + 243*a₀^2*H₀^6*wₐ*Ω^3/2 - 1629*a₀^2*H₀^6*wₐ*Ω^2/2 + 2355*a₀^2*H₀^6*wₐ*Ω/2 - 969*a₀^2*H₀^6*wₐ/2 - 2*a₀^2*H₀^6*p^4*Ω^2 + 5*a₀^2*H₀^6*p^4*Ω - 3*a₀^2*H₀^6*p^4 - 3*a₀^2*H₀^6*p^3*Ω^3/2 + 119*a₀^2*H₀^6*p^3*Ω^2/4 - 60*a₀^2*H₀^6*p^3*Ω + 127*a₀^2*H₀^6*p^3/4 + 27*a₀^2*H₀^6*p^2*Ω^3/2 - 273*a₀^2*H₀^6*p^2*Ω^2/2 + 917*a₀^2*H₀^6*p^2*Ω/4 - 425*a₀^2*H₀^6*p^2/4 - 81*a₀^2*H₀^6*p*Ω^3/2 + 855*a₀^2*H₀^6*p*Ω^2/4 - 1097*a₀^2*H₀^6*p*Ω/4 + 101*a₀^2*H₀^6*p + 81*a₀^2*H₀^6*Ω^3/2 - 54*a₀^2*H₀^6*Ω^2 + 129*a₀^2*H₀^6*Ω/2 - 31*a₀^2*H₀^6 + 81*a₀*H₀^6*wₐ^4*Ω^3*D 0 t₀ - 1377*a₀*H₀^6*wₐ^4*Ω^2*D 0 t₀/2 + 1215*a₀*H₀^6*wₐ^4*Ω*D 0 t₀ - 1215*a₀*H₀^6*wₐ^4*D 0 t₀/2 - 108*a₀*H₀^6*wₐ^3*p*Ω^3*D 0 t₀ + 918*a₀*H₀^6*wₐ^3*p*Ω^2*D 0 t₀ - 1620*a₀*H₀^6*wₐ^3*p*Ω*D 0 t₀ + 810*a₀*H₀^6*wₐ^3*p*D 0 t₀ + 621*a₀*H₀^6*wₐ^3*Ω^3*D 0 t₀/2 - 10071*a₀*H₀^6*wₐ^3*Ω^2*D 0 t₀/4 + 4347*a₀*H₀^6*wₐ^3*Ω*D 0 t₀ - 8559*a₀*H₀^6*wₐ^3*D 0 t₀/4 + 54*a₀*H₀^6*wₐ^2*p^2*Ω^3*D 0 t₀ - 459*a₀*H₀^6*wₐ^2*p^2*Ω^2*D 0 t₀ + 810*a₀*H₀^6*wₐ^2*p^2*Ω*D 0 t₀ - 405*a₀*H₀^6*wₐ^2*p^2*D 0 t₀ - 603*a₀*H₀^6*wₐ^2*p*Ω^3*D 0 t₀/2 + 9441*a₀*H₀^6*wₐ^2*p*Ω^2*D 0 t₀/4 - 4005*a₀*H₀^6*wₐ^2*p*Ω*D 0 t₀ + 7785*a₀*H₀^6*wₐ^2*p*D 0 t₀/4 + 378*a₀*H₀^6*wₐ^2*Ω^3*D 0 t₀ - 9081*a₀*H₀^6*wₐ^2*Ω^2*D 0 t₀/4 + 12825*a₀*H₀^6*wₐ^2*Ω*D 0 t₀/4 - 1314*a₀*H₀^6*wₐ^2*D 0 t₀ - 12*a₀*H₀^6*wₐ*p^3*Ω^3*D 0 t₀ + 102*a₀*H₀^6*wₐ*p^3*Ω^2*D 0 t₀ - 180*a₀*H₀^6*wₐ*p^3*Ω*D 0 t₀ + 90*a₀*H₀^6*wₐ*p^3*D 0 t₀ + 195*a₀*H₀^6*wₐ*p^2*Ω^3*D 0 t₀/2 - 2937*a₀*H₀^6*wₐ*p^2*Ω^2*D 0 t₀/4 + 1221*a₀*H₀^6*wₐ*p^2*Ω*D 0 t₀ - 2337*a₀*H₀^6*wₐ*p^2*D 0 t₀/4 - 234*a₀*H₀^6*wₐ*p*Ω^3*D 0 t₀ + 4965*a₀*H₀^6*wₐ*p*Ω^2*D 0 t₀/4 - 1590*a₀*H₀^6*wₐ*p*Ω*D 0 t₀ + 2331*a₀*H₀^6*wₐ*p*D 0 t₀/4 + 297*a₀*H₀^6*wₐ*Ω^3*D 0 t₀/2 - 801*a₀*H₀^6*wₐ*Ω^2*D 0 t₀/2 + 861*a₀*H₀^6*wₐ*Ω*D 0 t₀/2 - 357*a₀*H₀^6*wₐ*D 0 t₀/2 + a₀*H₀^6*p^4*Ω^3*D 0 t₀ - 17*a₀*H₀^6*p^4*Ω^2*D 0 t₀/2 + 15*a₀*H₀^6*p^4*Ω*D 0 t₀ - 15*a₀*H₀^6*p^4*D 0 t₀/2 - 21*a₀*H₀^6*p^3*Ω^3*D 0 t₀/2 + 303*a₀*H₀^6*p^3*Ω^2*D 0 t₀/4 - 123*a₀*H₀^6*p^3*Ω*D 0 t₀ + 231*a₀*H₀^6*p^3*D 0 t₀/4 + 36*a₀*H₀^6*p^2*Ω^3*D 0 t₀ - 327*a₀*H₀^6*p^2*Ω^2*D 0 t₀/2 + 723*a₀*H₀^6*p^2*Ω*D 0 t₀/4 - 213*a₀*H₀^6*p^2*D 0 t₀/4 - 81*a₀*H₀^6*p*Ω^3*D 0 t₀/2 + 171*a₀*H₀^6*p*Ω^2*D 0 t₀/4 - 93*a₀*H₀^6*p*Ω*D 0 t₀/4 + 21*a₀*H₀^6*p*D 0 t₀ - 27*a₀*H₀^6*Ω^2*D 0 t₀/2 + 33*a₀*H₀^6*Ω*D 0 t₀/2 - 3*a₀*H₀^6*D 0 t₀ + 2*a₀*H₀*D 5 t₀ + 81*H₀^6*wₐ^4*Ω^3*D 0 t₀^2 - 1377*H₀^6*wₐ^4*Ω^2*D 0 t₀^2/2 + 1215*H₀^6*wₐ^4*Ω*D 0 t₀^2 - 1215*H₀^6*wₐ^4*D 0 t₀^2/2 - 108*H₀^6*wₐ^3*p*Ω^3*D 0 t₀^2 + 918*H₀^6*wₐ^3*p*Ω^2*D 0 t₀^2 - 1620*H₀^6*wₐ^3*p*Ω*D 0 t₀^2 + 810*H₀^6*wₐ^3*p*D 0 t₀^2 + 675*H₀^6*wₐ^3*Ω^3*D 0 t₀^2/4 - 999*H₀^6*wₐ^3*Ω^2*D 0 t₀^2 + 5643*H₀^6*wₐ^3*Ω*D 0 t₀^2/4 - 1161*H₀^6*wₐ^3*D 0 t₀^2/2 + 54*H₀^6*wₐ^2*p^2*Ω^3*D 0 t₀^2 - 459*H₀^6*wₐ^2*p^2*Ω^2*D 0 t₀^2 + 810*H₀^6*wₐ^2*p^2*Ω*D 0 t₀^2 - 405*H₀^6*wₐ^2*p^2*D 0 t₀^2 - 639*H₀^6*wₐ^2*p*Ω^3*D 0 t₀^2/4 + 1683*H₀^6*wₐ^2*p*Ω^2*D 0 t₀^2/2 - 4275*H₀^6*wₐ^2*p*Ω*D 0 t₀^2/4 + 387*H₀^6*wₐ^2*p*D 0 t₀^2 + 351*H₀^6*wₐ^2*Ω^3*D 0 t₀^2/4 - 981*H₀^6*wₐ^2*Ω^2*D 0 t₀^2/4 + 270*H₀^6*wₐ^2*Ω*D 0 t₀^2 - 225*H₀^6*wₐ^2*D 0 t₀^2/2 - 12*H₀^6*wₐ*p^3*Ω^3*D 0 t₀^2 + 102*H₀^6*wₐ*p^3*Ω^2*D 0 t₀^2 - 180*H₀^6*wₐ*p^3*Ω*D 0 t₀^2 + 90*H₀^6*wₐ*p^3*D 0 t₀^2 + 201*H₀^6*wₐ*p^2*Ω^3*D 0 t₀^2/4 - 228*H₀^6*wₐ*p^2*Ω^2*D 0 t₀^2 + 969*H₀^6*wₐ*p^2*Ω*D 0 t₀^2/4 - 129*H₀^6*wₐ*p^2*D 0 t₀^2/2 - 171*H₀^6*wₐ*p*Ω^3*D 0 t₀^2/4 + 57*H₀^6*wₐ*p*Ω^2*D 0 t₀^2/2 - 33*H₀^6*wₐ*p*Ω*D 0 t₀^2/4 + 45*H₀^6*wₐ*p*D 0 t₀^2/2 - 27*H₀^6*wₐ*Ω^2*D 0 t₀^2/2 + 33*H₀^6*wₐ*Ω*D 0 t₀^2/2 - 3*H₀^6*wₐ*D 0 t₀^2 + H₀^6*p^4*Ω^3*D 0 t₀^2 - 17*H₀^6*p^4*Ω^2*D 0 t₀^2/2 + 15*H₀^6*p^4*Ω*D 0 t₀^2 - 15*H₀^6*p^4*D 0 t₀^2/2 - 21*H₀^6*p^3*Ω^3*D 0 t₀^2/4 + 39*H₀^6*p^3*Ω^2*D 0 t₀^2/2 - 57*H₀^6*p^3*Ω*D 0 t₀^2/4 + 9*H₀^6*p^2*Ω^3*D 0 t₀^2/2 + 63*H₀^6*p^2*Ω^2*D 0 t₀^2/4 - 81*H₀^6*p^2*Ω*D 0 t₀^2/4 + 27*H₀^6*p*Ω^3*D 0 t₀^2/4 + 27*H₀^6*p*Ω^2*D 0 t₀^2/4 - 27*H₀^6*p*Ω*D 0 t₀^2/2) * he_d0 - (1431*a₀^2*H₀^5*wₐ^3*Ω^2/4 - 837*a₀^2*H₀^5*wₐ^3*Ω + 1917*a₀^2*H₀^5*wₐ^3/4 - 1431*a₀^2*H₀^5*wₐ^2*p*Ω^2/4 + 837*a₀^2*H₀^5*wₐ^2*p*Ω - 1917*a₀^2*H₀^5*wₐ^2*p/4 + 3339*a₀^2*H₀^5*wₐ^2*Ω^2/4 - 7173*a₀^2*H₀^5*wₐ^2*Ω/4 + 1917*a₀^2*H₀^5*wₐ^2/2 + 477*a₀^2*H₀^5*wₐ*p^2*Ω^2/4 - 279*a₀^2*H₀^5*wₐ*p^2*Ω + 639*a₀^2*H₀^5*wₐ*p^2/4 - 2067*a₀^2*H₀^5*wₐ*p*Ω^2/4 + 2151*a₀^2*H₀^5*wₐ*p*Ω/2 - 2235*a₀^2*H₀^5*wₐ*p/4 + 423*a₀^2*H₀^5*wₐ*Ω^2 - 1551*a₀^2*H₀^5*wₐ*Ω/2 + 705*a₀^2*H₀^5*wₐ/2 - 53*a₀^2*H₀^5*p^3*Ω^2/4 + 31*a₀^2*H₀^5*p^3*Ω - 71*a₀^2*H₀^5*p^3/4 + 159*a₀^2*H₀^5*p^2*Ω^2/2 - 637*a₀^2*H₀^5*p^2*Ω/4 + 319*a₀^2*H₀^5*p^2/4 - 405*a₀^2*H₀^5*p*Ω^2/4 + 697*a₀^2*H₀^5*p*Ω/4 - 73*a₀^2*H₀^5*p - 54*a₀^2*H₀^5*Ω^2 - 33*a₀^2*H₀^5*Ω/2 + 17*a₀^2*H₀^5 - 594*a₀*H₀^5*wₐ^2*Ω^2*D 0 t₀ + 1512*a₀*H₀^5*wₐ^2*Ω*D 0 t₀ - 918*a₀*H₀^5*wₐ^2*D 0 t₀ + 396*a₀*H₀^5*wₐ*p*Ω^2*D 0 t₀ - 1008*a₀*H₀^5*wₐ*p*Ω*D 0 t₀ + 612*a₀*H₀^5*wₐ*p*D 0 t₀ - 630*a₀*H₀^5*wₐ*Ω^2*D 0 t₀ + 1098*a₀*H₀^5*wₐ*Ω*D 0 t₀ - 468*a₀*H₀^5*wₐ*D 0 t₀ - 66*a₀*H₀^5*p^2*Ω^2*D 0 t₀ + 168*a₀*H₀^5*p^2*Ω*D 0 t₀ - 102*a₀*H₀^5*p^2*D 0 t₀ + 198*a₀*H₀^5*p*Ω^2*D 0 t₀ - 306*a₀*H₀^5*p*Ω*D 0 t₀ + 108*a₀*H₀^5*p*D 0 t₀ + 24*a₀*H₀^5*Ω*D 0 t₀ - 24*a₀*H₀^5*D 0 t₀ + 243*a₀*H₀^4*wₐ^3*Ω^2*D 1 t₀/4 - 243*a₀*H₀^4*wₐ^3*Ω*D 1 t₀ + 729*a₀*H₀^4*wₐ^3*D 1 t₀/4 - 243*a₀*H₀^4*wₐ^2*p*Ω^2*D 1 t₀/4 + 243*a₀*H₀^4*wₐ^2*p*Ω*D 1 t₀ - 729*a₀*H₀^4*wₐ^2*p*D 1 t₀/4 + 567*a₀*H₀^4*wₐ^2*Ω^2*D 1 t₀/4 - 2025*a₀*H₀^4*wₐ^2*Ω*D 1 t₀/4 + 729*a₀*H₀^4*wₐ^2*D 1 t₀/2 + 81*a₀*H₀^4*wₐ*p^2*Ω^2*D 1 t₀/4 - 81*a₀*H₀^4*wₐ*p^2*Ω*D 1 t₀ + 243*a₀*H₀^4*wₐ*p^2*D 1 t₀/4 - 351*a₀*H₀^4*wₐ*p*Ω^2*D 1 t₀/4 + 567*a₀*H₀^4*wₐ*p*Ω*D 1 t₀/2 - 783*a₀*H₀^4*wₐ*p*D 1 t₀/4 + 27*a₀*H₀^4*wₐ*Ω^2*D 1 t₀ - 99*a₀*H₀^4*wₐ*Ω*D 1 t₀/2 + 45*a₀*H₀^4*wₐ*D 1 t₀/2 - 9*a₀*H₀^4*p^3*Ω^2*D 1 t₀/4 + 9*a₀*H₀^4*p^3*Ω*D 1 t₀ - 27*a₀*H₀^4*p^3*D 1 t₀/4 + 27*a₀*H₀^4*p^2*Ω^2*D 1 t₀/2 - 153*a₀*H₀^4*p^2*Ω*D 1 t₀/4 + 99*a₀*H₀^4*p^2*D 1 t₀/4 - 9*a₀*H₀^4*p*Ω^2*D 1 t₀/4 - 51*a₀*H₀^4*p*Ω*D 1 t₀/4 + 15*a₀*H₀^4*p*D 1 t₀ - 54*a₀*H₀^4*Ω^2*D 1 t₀ + 99*a₀*H₀^4*Ω*D 1 t₀/2 - 27*a₀*H₀^4*D 1 t₀ - 648*H₀^5*wₐ^3*Ω^2*D 0 t₀^2 + 1620*H₀^5*wₐ^3*Ω*D 0 t₀^2 - 972*H₀^5*wₐ^3*D 0 t₀^2 + 648*H₀^5*wₐ^2*p*Ω^2*D 0 t₀^2 - 1620*H₀^5*wₐ^2*p*Ω*D 0 t₀^2 + 972*H₀^5*wₐ^2*p*D 0 t₀^2 - 702*H₀^5*wₐ^2*Ω^2*D 0 t₀^2 + 1242*H₀^5*wₐ^2*Ω*D 0 t₀^2 - 540*H₀^5*wₐ^2*D 0 t₀^2 - 216*H₀^5*wₐ*p^2*Ω^2*D 0 t₀^2 + 540*H₀^5*wₐ*p^2*Ω*D 0 t₀^2 - 324*H₀^5*wₐ*p^2*D 0 t₀^2 + 396*H₀^5*wₐ*p*Ω^2*D 0 t₀^2 - 576*H₀^5*wₐ*p*Ω*D 0 t₀^2 + 180*H₀^5*wₐ*p*D 0 t₀^2 + 36*H₀^5*wₐ*Ω*D 0 t₀^2 - 36*H₀^5*wₐ*D 0 t₀^2 + 24*H₀^5*p^3*Ω^2*D 0 t₀^2 - 60*H₀^5*p^3*Ω*D 0 t₀^2 + 36*H₀^5*p^3*D 0 t₀^2 - 54*H₀^5*p^2*Ω^2*D 0 t₀^2 + 54*H₀^5*p^2*Ω*D 0 t₀^2 - 54*H₀^5*p*Ω^2*D 0 t₀^2 + 54*H₀^5*p*Ω*D 0 t₀^2 - 162*H₀^4*wₐ^2*Ω^2*D 0 t₀*D 1 t₀ + 648*H₀^4*wₐ^2*Ω*D 0 t₀*D 1 t₀ - 486*H₀^4*wₐ^2*D 0 t₀*D 1 t₀ + 108*H₀^4*wₐ*p*Ω^2*D 0 t₀*D 1 t₀ - 432*H₀^4*wₐ*p*Ω*D 0 t₀*D 1 t₀ + 324*H₀^4*wₐ*p*D 0 t₀*D 1 t₀ - 162*H₀^4*wₐ*Ω^2*D 0 t₀*D 1 t₀ + 270*H₀^4*wₐ*Ω*D 0 t₀*D 1 t₀ - 108*H₀^4*wₐ*D 0 t₀*D 1 t₀ - 18*H₀^4*p^2*Ω^2*D 0 t₀*D 1 t₀ + 72*H₀^4*p^2*Ω*D 0 t₀*D 1 t₀ - 54*H₀^4*p^2*D 0 t₀*D 1 t₀ + 54*H₀^4*p*Ω^2*D 0 t₀*D 1 t₀ - 54*H₀^4*p*Ω*D 0 t₀*D 1 t₀ + 72*H₀^3*wₐ*Ω*D 1 t₀^2 - 72*H₀^3*wₐ*D 1 t₀^2 - 24*H₀^3*p*Ω*D 1 t₀^2 + 24*H₀^3*p*D 1 t₀^2 + 2*D 0 t₀*D 5 t₀) * he_d1 - (81*a₀^2*H₀^6*wₐ^2*Ω^3*D 0 t₀/2 - 243*a₀^2*H₀^6*wₐ^2*Ω^2*D 0 t₀/2 + 243*a₀^2*H₀^6*wₐ^2*Ω*D 0 t₀/2 - 81*a₀^2*H₀^6*wₐ^2*D 0 t₀/2 - 27*a₀^2*H₀^6*wₐ*p*Ω^3*D 0 t₀ + 81*a₀^2*H₀^6*wₐ*p*Ω^2*D 0 t₀ - 81*a₀^2*H₀^6*wₐ*p*Ω*D 0 t₀ + 27*a₀^2*H₀^6*wₐ*p*D 0 t₀ + 81*a₀^2*H₀^6*wₐ*Ω^3*D 0 t₀ - 216*a₀^2*H₀^6*wₐ*Ω^2*D 0 t₀ + 189*a₀^2*H₀^6*wₐ*Ω*D 0 t₀ - 54*a₀^2*H₀^6*wₐ*D 0 t₀ + 9*a₀^2*H₀^6*p^2*Ω^3*D 0 t₀/2 - 27*a₀^2*H₀^6*p^2*Ω^2*D 0 t₀/2 + 27*a₀^2*H₀^6*p^2*Ω*D 0 t₀/2 - 9*a₀^2*H₀^6*p^2*D 0 t₀/2 - 27*a₀^2*H₀^6*p*Ω^3*D 0 t₀ + 72*a₀^2*H₀^6*p*Ω^2*D 0 t₀ - 63*a₀^2*H₀^6*p*Ω*D 0 t₀ + 18*a₀^2*H₀^6*p*D 0 t₀ + 81*a₀^2*H₀^6*Ω^3*D 0 t₀/2 - 189*a₀^2*H₀^6*Ω^2*D 0 t₀/2 + 72*a₀^2*H₀^6*Ω*D 0 t₀ - 18*a₀^2*H₀^6*D 0 t₀ + 81*a₀*H₀^6*wₐ^3*Ω^3*D 0 t₀^2/4 - 405*a₀*H₀^6*wₐ^3*Ω^2*D 0 t₀^2/4 + 567*a₀*H₀^6*wₐ^3*Ω*D 0 t₀^2/4 - 243*a₀*H₀^6*wₐ^3*D 0 t₀^2/4 - 81*a₀*H₀^6*wₐ^2*p*Ω^3*D 0 t₀^2/4 + 405*a₀*H₀^6*wₐ^2*p*Ω^2*D 0 t₀^2/4 - 567*a₀*H₀^6*wₐ^2*p*Ω*D 0 t₀^2/4 + 243*a₀*H₀^6*wₐ^2*p*D 0 t₀^2/4 + 189*a₀*H₀^6*wₐ^2*Ω^3*D 0 t₀^2/4 - 216*a₀*H₀^6*wₐ^2*Ω^2*D 0 t₀^2 + 1161*a₀*H₀^6*wₐ^2*Ω*D 0 t₀^2/4 - 243*a₀*H₀^6*wₐ^2*D 0 t₀^2/2 + 27*a₀*H₀^6*wₐ*p^2*Ω^3*D 0 t₀^2/4 - 135*a₀*H₀^6*wₐ*p^2*Ω^2*D 0 t₀^2/4 + 189*a₀*H₀^6*wₐ*p^2*Ω*D 0 t₀^2/4 - 81*a₀*H₀^6*wₐ*p^2*D 0 t₀^2/4 - 117*a₀*H₀^6*wₐ*p*Ω^3*D 0 t₀^2/4 + 495*a₀*H₀^6*wₐ*p*Ω^2*D 0 t₀^2/4 - 639*a₀*H₀^6*wₐ*p*Ω*D 0 t₀^2/4 + 261*a₀*H₀^6*wₐ*p*D 0 t₀^2/4 + 27*a₀*H₀^6*wₐ*Ω^3*D 0 t₀^2 - 207*a₀*H₀^6*wₐ*Ω^2*D 0 t₀^2/2 + 126*a₀*H₀^6*wₐ*Ω*D 0 t₀^2 - 99*a₀*H₀^6*wₐ*D 0 t₀^2/2 - 3*a₀*H₀^6*p^3*Ω^3*D 0 t₀^2/4 + 15*a₀*H₀^6*p^3*Ω^2*D 0 t₀^2/4 - 21*a₀*H₀^6*p^3*Ω*D 0 t₀^2/4 + 9*a₀*H₀^6*p^3*D 0 t₀^2/4 + 9*a₀*H₀^6*p^2*Ω^3*D 0 t₀^2/2 - 69*a₀*H₀^6*p^2*Ω^2*D 0 t₀^2/4 + 21*a₀*H₀^6*p^2*Ω*D 0 t₀^2 - 33*a₀*H₀^6*p^2*D 0 t₀^2/4 - 27*a₀*H₀^6*p*Ω^3*D 0 t₀^2/4 + 45*a₀*H₀^6*p*Ω^2*D 0 t₀^2/2 - 99*a₀*H₀^6*p*Ω*D 0 t₀^2/4 + 9*a₀*H₀^6*p*D 0 t₀^2 - 27*a₀*H₀^6*Ω^2*D 0 t₀^2/2 + 33*a₀*H₀^6*Ω*D 0 t₀^2/2 - 3*a₀*H₀^6*D 0 t₀^2 - 108*a₀*H₀^5*wₐ^2*Ω^2*D 0 t₀*D 1 t₀ + 216*a₀*H₀^5*wₐ^2*Ω*D 0 t₀*D 1 t₀ - 108*a₀*H₀^5*wₐ^2*D 0 t₀*D 1 t₀ + 72*a₀*H₀^5*wₐ*p*Ω^2*D 0 t₀*D 1 t₀ - 144*a₀*H₀^5*wₐ*p*Ω*D 0 t₀*D 1 t₀ + 72*a₀*H₀^5*wₐ*p*D 0 t₀*D 1 t₀ - 144*a₀*H₀^5*wₐ*Ω^2*D 0 t₀*D 1 t₀ + 288*a₀*H₀^5*wₐ*Ω*D 0 t₀*D 1 t₀ - 144*a₀*H₀^5*wₐ*D 0 t₀*D 1 t₀ - 12*a₀*H₀^5*p^2*Ω^2*D 0 t₀*D 1 t₀ + 24*a₀*H₀^5*p^2*Ω*D 0 t₀*D 1 t₀ - 12*a₀*H₀^5*p^2*D 0 t₀*D 1 t₀ + 36*a₀*H₀^5*p*Ω^2*D 0 t₀*D 1 t₀ - 72*a₀*H₀^5*p*Ω*D 0 t₀*D 1 t₀ + 36*a₀*H₀^5*p*D 0 t₀*D 1 t₀ + 24*a₀*H₀^5*Ω*D 0 t₀*D 1 t₀ - 24*a₀*H₀^5*D 0 t₀*D 1 t₀ - 54*a₀*H₀^4*wₐ*Ω^2*D 1 t₀^2 + 108*a₀*H₀^4*wₐ*Ω*D 1 t₀^2 - 54*a₀*H₀^4*wₐ*D 1 t₀^2 + 18*a₀*H₀^4*p*Ω^2*D 1 t₀^2 - 36*a₀*H₀^4*p*Ω*D 1 t₀^2 + 18*a₀*H₀^4*p*D 1 t₀^2 - 54*a₀*H₀^4*Ω^2*D 1 t₀^2 + 90*a₀*H₀^4*Ω*D 1 t₀^2 - 36*a₀*H₀^4*D 1 t₀^2) * he_g0 - (-54*a₀*H₀^5*wₐ^2*Ω^2*D 0 t₀^2 + 108*a₀*H₀^5*wₐ^2*Ω*D 0 t₀^2 - 54*a₀*H₀^5*wₐ^2*D 0 t₀^2 + 36*a₀*H₀^5*wₐ*p*Ω^2*D 0 t₀^2 - 72*a₀*H₀^5*wₐ*p*Ω*D 0 t₀^2 + 36*a₀*H₀^5*wₐ*p*D 0 t₀^2 - 72*a₀*H₀^5*wₐ*Ω^2*D 0 t₀^2 + 144*a₀*H₀^5*wₐ*Ω*D 0 t₀^2 - 72*a₀*H₀^5*wₐ*D 0 t₀^2 - 6*a₀*H₀^5*p^2*Ω^2*D 0 t₀^2 + 12*a₀*H₀^5*p^2*Ω*D 0 t₀^2 - 6*a₀*H₀^5*p^2*D 0 t₀^2 + 18*a₀*H₀^5*p*Ω^2*D 0 t₀^2 - 36*a₀*H₀^5*p*Ω*D 0 t₀^2 + 18*a₀*H₀^5*p*D 0 t₀^2 + 12*a₀*H₀^5*Ω*D 0 t₀^2 - 12*a₀*H₀^5*D 0 t₀^2 - 108*a₀*H₀^4*wₐ*Ω^2*D 0 t₀*D 1 t₀ + 216*a₀*H₀^4*wₐ*Ω*D 0 t₀*D 1 t₀ - 108*a₀*H₀^4*wₐ*D 0 t₀*D 1 t₀ + 36*a₀*H₀^4*p*Ω^2*D 0 t₀*D 1 t₀ - 72*a₀*H₀^4*p*Ω*D 0 t₀*D 1 t₀ + 36*a₀*H₀^4*p*D 0 t₀*D 1 t₀ - 108*a₀*H₀^4*Ω^2*D 0 t₀*D 1 t₀ + 180*a₀*H₀^4*Ω*D 0 t₀*D 1 t₀ - 72*a₀*H₀^4*D 0 t₀*D 1 t₀ + 24*H₀^2*Ω*D 1 t₀^3 - 24*H₀^2*D 1 t₀^3) * he_g1 - (27*a₀^2*H₀^4*wₐ^2*Ω^2 - 54*a₀^2*H₀^4*wₐ^2*Ω + 27*a₀^2*H₀^4*wₐ^2 - 18*a₀^2*H₀^4*wₐ*p*Ω^2 + 36*a₀^2*H₀^4*wₐ*p*Ω - 18*a₀^2*H₀^4*wₐ*p + 54*a₀^2*H₀^4*wₐ*Ω^2 - 90*a₀^2*H₀^4*wₐ*Ω + 36*a₀^2*H₀^4*wₐ + 3*a₀^2*H₀^4*p^2*Ω^2 - 6*a₀^2*H₀^4*p^2*Ω + 3*a₀^2*H₀^4*p^2 - 18*a₀^2*H₀^4*p*Ω^2 + 30*a₀^2*H₀^4*p*Ω - 12*a₀^2*H₀^4*p + 27*a₀^2*H₀^4*Ω^2 - 36*a₀^2*H₀^4*Ω + 12*a₀^2*H₀^4 + 54*a₀*H₀^4*wₐ^3*Ω^2*D 0 t₀ - 216*a₀*H₀^4*wₐ^3*Ω*D 0 t₀ + 162*a₀*H₀^4*wₐ^3*D 0 t₀ - 54*a₀*H₀^4*wₐ^2*p*Ω^2*D 0 t₀ + 216*a₀*H₀^4*wₐ^2*p*Ω*D 0 t₀ - 162*a₀*H₀^4*wₐ^2*p*D 0 t₀ + 126*a₀*H₀^4*wₐ^2*Ω^2*D 0 t₀ - 450*a₀*H₀^4*wₐ^2*Ω*D 0 t₀ + 324*a₀*H₀^4*wₐ^2*D 0 t₀ + 18*a₀*H₀^4*wₐ*p^2*Ω^2*D 0 t₀ - 72*a₀*H₀^4*wₐ*p^2*Ω*D 0 t₀ + 54*a₀*H₀^4*wₐ*p^2*D 0 t₀ - 78*a₀*H₀^4*wₐ*p*Ω^2*D 0 t₀ + 252*a₀*H₀^4*wₐ*p*Ω*D 0 t₀ - 174*a₀*H₀^4*wₐ*p*D 0 t₀ - 27*a₀*H₀^4*wₐ*Ω^2*D 0 t₀*G 0 t₀ + 72*a₀*H₀^4*wₐ*Ω^2*D 0 t₀ + 54*a₀*H₀^4*wₐ*Ω*D 0 t₀*G 0 t₀ - 204*a₀*H₀^4*wₐ*Ω*D 0 t₀ - 27*a₀*H₀^4*wₐ*D 0 t₀*G 0 t₀ + 132*a₀*H₀^4*wₐ*D 0 t₀ - 2*a₀*H₀^4*p^3*Ω^2*D 0 t₀ + 8*a₀*H₀^4*p^3*Ω*D 0 t₀ - 6*a₀*H₀^4*p^3*D 0 t₀ + 12*a₀*H₀^4*p^2*Ω^2*D 0 t₀ - 34*a₀*H₀^4*p^2*Ω*D 0 t₀ + 22*a₀*H₀^4*p^2*D 0 t₀ + 9*a₀*H₀^4*p*Ω^2*D 0 t₀*G 0 t₀ - 18*a₀*H₀^4*p*Ω^2*D 0 t₀ - 18*a₀*H₀^4*p*Ω*D 0 t₀*G 0 t₀ + 42*a₀*H₀^4*p*Ω*D 0 t₀ + 9*a₀*H₀^4*p*D 0 t₀*G 0 t₀ - 24*a₀*H₀^4*p*D 0 t₀ - 27*a₀*H₀^4*Ω^2*D 0 t₀*G 0 t₀ + 45*a₀*H₀^4*Ω*D 0 t₀*G 0 t₀ - 36*a₀*H₀^4*Ω*D 0 t₀ - 18*a₀*H₀^4*D 0 t₀*G 0 t₀ + 8*a₀*H₀^4*D 0 t₀ - 198*a₀*H₀^3*wₐ^2*Ω*D 1 t₀ + 198*a₀*H₀^3*wₐ^2*D 1 t₀ + 132*a₀*H₀^3*wₐ*p*Ω*D 1 t₀ - 132*a₀*H₀^3*wₐ*p*D 1 t₀ - 264*a₀*H₀^3*wₐ*Ω*D 1 t₀ + 264*a₀*H₀^3*wₐ*D 1 t₀ - 22*a₀*H₀^3*p^2*Ω*D 1 t₀ + 22*a₀*H₀^3*p^2*D 1 t₀ + 66*a₀*H₀^3*p*Ω*D 1 t₀ - 66*a₀*H₀^3*p*D 1 t₀ + 44*a₀*H₀^3*D 1 t₀ - 18*a₀*H₀^2*wₐ*Ω*D 2 t₀ + 18*a₀*H₀^2*wₐ*D 2 t₀ + 6*a₀*H₀^2*p*Ω*D 2 t₀ - 6*a₀*H₀^2*p*D 2 t₀ - 18*a₀*H₀^2*Ω*D 2 t₀ + 12*a₀*H₀^2*D 2 t₀ - 81*H₀^4*wₐ^2*Ω^2*D 0 t₀^2 + 324*H₀^4*wₐ^2*Ω*D 0 t₀^2 - 243*H₀^4*wₐ^2*D 0 t₀^2 + 54*H₀^4*wₐ*p*Ω^2*D 0 t₀^2 - 216*H₀^4*wₐ*p*Ω*D 0 t₀^2 + 162*H₀^4*wₐ*p*D 0 t₀^2 - 81*H₀^4*wₐ*Ω^2*D 0 t₀^2 + 135*H₀^4*wₐ*Ω*D 0 t₀^2 - 54*H₀^4*wₐ*D 0 t₀^2 - 9*H₀^4*p^2*Ω^2*D 0 t₀^2 + 36*H₀^4*p^2*Ω*D 0 t₀^2 - 27*H₀^4*p^2*D 0 t₀^2 + 27*H₀^4*p*Ω^2*D 0 t₀^2 - 27*H₀^4*p*Ω*D 0 t₀^2 + 72*H₀^2*Ω*D 0 t₀*D 1 t₀*G 1 t₀ + 18*H₀^2*Ω*D 0 t₀*D 2 t₀*G 0 t₀ + 36*H₀^2*Ω*D 1 t₀^2*G 0 t₀ - 72*H₀^2*D 0 t₀*D 1 t₀*G 1 t₀ - 18*H₀^2*D 0 t₀*D 2 t₀*G 0 t₀ - 36*H₀^2*D 1 t₀^2*G 0 t₀ + 12*D 2 t₀^2) * he_d2 - (18*H₀^2*Ω*D 0 t₀^2*D 2 t₀ + 36*H₀^2*Ω*D 0 t₀*D 1 t₀^2 - 18*H₀^2*D 0 t₀^2*D 2 t₀ - 36*H₀^2*D 0 t₀*D 1 t₀^2) * he_g2 - (-27*a₀*H₀^3*wₐ^2*Ω*D 0 t₀ + 27*a₀*H₀^3*wₐ^2*D 0 t₀ + 18*a₀*H₀^3*wₐ*p*Ω*D 0 t₀ - 18*a₀*H₀^3*wₐ*p*D 0 t₀ - 36*a₀*H₀^3*wₐ*Ω*D 0 t₀ + 36*a₀*H₀^3*wₐ*D 0 t₀ - 3*a₀*H₀^3*p^2*Ω*D 0 t₀ + 3*a₀*H₀^3*p^2*D 0 t₀ + 9*a₀*H₀^3*p*Ω*D 0 t₀ - 9*a₀*H₀^3*p*D 0 t₀ + 6*a₀*H₀^3*D 0 t₀ + 12*H₀^2*Ω*D 0 t₀^2*G 1 t₀ + 24*H₀^2*Ω*D 0 t₀*D 1 t₀*G 0 t₀ - 12*H₀^2*D 0 t₀^2*G 1 t₀ - 24*H₀^2*D 0 t₀*D 1 t₀*G 0 t₀ + 6*D 0 t₀*D 3 t₀ + 44*D 1 t₀*D 2 t₀) * he_d3 - (12*H₀^2*Ω*D 0 t₀^2*D 1 t₀ - 12*H₀^2*D 0 t₀^2*D 1 t₀) * he_g3 - (3*H₀^2*Ω*D 0 t₀^2*G 0 t₀ - 3*H₀^2*D 0 t₀^2*G 0 t₀ + 8*D 0 t₀*D 2 t₀ + 9*D 1 t₀^2) * he_d4 - (H₀^2*Ω*D 0 t₀^3 - H₀^2*D 0 t₀^3) * he_g4
    have hl : (2*a₀^2*H₀) ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)
  have hH0 : H₀ ≠ 0 := hH.ne'
  have cc : ∀ n, cosmoCoeff n a t₀ = D n t₀ / (a₀ * H₀ ^ n) := fun n => by
    rw [cosmoCoeff, iteratedDeriv_eq_iterate]
  have hdec : decel a t₀ = -(D 2 t₀ * a₀) / D 1 t₀ ^ 2 := rfl
  subst hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdec, he_d2, he_d1]; field_simp; ring
  · rw [cc, he_d3]; field_simp; ring
  · rw [cc, he_d4]; field_simp; ring
  · rw [cc, he_d5]; field_simp; ring

/-- The printed `l₀` is wrong in every flat CPL model with `(1 − Ω)(7 − Ω) wₐ ≠ 0`. -/
theorem printedL0_ne (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatCPL Ω w₀ wₐ a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) (hne : (1 - Ω) * (7 - Ω) * wₐ ≠ 0) :
    cosmoCoeff 5 a t₀ ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := by
  intro h
  rw [(flatCPL_coeffs Ω w₀ wₐ a t₀ hL hs).2.2.2] at h
  apply hne
  have h2 : (1 - Ω) * (7 - Ω) * wₐ ^ 2 = 0 := by linear_combination h / 2
  have h3 : ((1 - Ω) * (7 - Ω) * wₐ) ^ 2 = 0 := by linear_combination (1 - Ω) * (7 - Ω) * h2
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h3

/-! ## An explicit flat CPL model: Ω = 0, w₀ = −1, wₐ = 2/3, a(t) = 1 − log(1 − t)

With Ω = 0 and 3(1 + w₀ + wₐ) = 2 the law is ȧ = H₀ a₀ exp(−(3wₐ/2)(1 − a/a₀)), solved in closed
form by a logarithm. -/

/-- The witness scale factor. -/
noncomputable def cplW : ℝ → ℝ := fun t => 1 - Real.log (1 - t)

lemma hasDerivAt_cplW {t : ℝ} (ht : t < 1) : HasDerivAt cplW (1 / (1 - t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h2 := (h1.log (by linarith)).const_sub 1
  have e : (-(-1 / (1 - t)) : ℝ) = 1 / (1 - t) := by ring
  rw [e] at h2
  exact h2

lemma cplW_zero : cplW 0 = 1 := by simp [cplW]

lemma hubble_cplW {t : ℝ} (ht : t < 1) : hubble cplW t = 1 / (1 - t) / cplW t := by
  rw [hubble, (hasDerivAt_cplW ht).deriv]

lemma hubble_cplW_zero : hubble cplW 0 = 1 := by
  rw [hubble_cplW (by norm_num), cplW_zero]; norm_num

lemma contDiffAt_cplW (n : WithTop ℕ∞) {t : ℝ} (ht : t < 1) : ContDiffAt ℝ n cplW t :=
  contDiffAt_const.sub ((contDiffAt_const.sub contDiffAt_id).log (by simp; linarith))

/-- The witness obeys the flat CPL law (17) with Ω = 0, w₀ = −1, wₐ = 2/3, at t₀ = 0. -/
theorem cplW_isFlatCPL : IsFlatCPL 0 (-1) (2 / 3) cplW 0 := by
  refine ⟨by rw [hubble_cplW_zero]; norm_num, ?_⟩
  have hc : ContinuousAt cplW 0 := (contDiffAt_cplW 0 (by norm_num)).continuousAt
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < cplW t :=
    hc.eventually (lt_mem_nhds (by rw [cplW_zero]; norm_num))
  filter_upwards [hpos, gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t hat ht
  refine ⟨hat, (hasDerivAt_cplW ht).differentiableAt, ?_⟩
  have hu : 0 < 1 - t := by linarith
  have hz : 1 + redshift cplW 0 t = 1 / cplW t := by
    rw [redshift, cplW_zero]; ring
  have hexp : -(3 * (2 / 3 : ℝ) * redshift cplW 0 t) / (1 + redshift cplW 0 t) =
      -(2 * Real.log (1 - t)) := by
    rw [hz, redshift, cplW_zero]
    have : cplW t = 1 - Real.log (1 - t) := rfl
    field_simp
    rw [this]; ring
  have hpow : (3 * (1 + -1 + 2 / 3) : ℝ) = 2 := by norm_num
  have he : Real.exp (-(2 * Real.log (1 - t))) = ((1 - t) ^ 2)⁻¹ := by
    rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hu]; ring
  rw [hexp, hz, hpow, Real.rpow_two, he, hubble_cplW_zero, hubble_cplW ht]
  have hsq : (0 : ℝ) * (1 / cplW t) ^ 3 + (1 - 0) * (1 / cplW t) ^ 2 * ((1 - t) ^ 2)⁻¹ =
      (1 / (1 - t) / cplW t) ^ 2 := by
    field_simp
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]
  ring

/-- **Refutation of the printed l₀ in Eq. (22)**, by an explicit flat CPL model
(Ω = 0, w₀ = −1, wₐ = 2/3, a(t) = 1 − log(1 − t), t₀ = 0): true l₀ = 24, printed 160/9. -/
theorem clsL0Claim_false : ¬ CLSL0Claim := by
  intro h
  have h1 := h 0 (-1) (2 / 3) cplW 0 cplW_isFlatCPL (contDiffAt_cplW 5 (by norm_num))
  rw [(flatCPL_coeffs 0 (-1) (2 / 3) cplW 0 cplW_isFlatCPL
    (contDiffAt_cplW 5 (by norm_num))).2.2.2] at h1
  norm_num at h1

end Work.Cosmography.CPL

