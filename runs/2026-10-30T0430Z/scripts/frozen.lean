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
  sorry

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
