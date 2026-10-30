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
  sorry

/-- **Refutation of the printed l₀ in Eq. (22)**, by an explicit flat CPL model
(Ω = 0, w₀ = −1, wₐ = 2/3, a(t) = 1 − log(1 − t), t₀ = 0): true l₀ = 24, printed 160/9. -/
theorem clsL0Claim_false : ¬ CLSL0Claim := by
  sorry

end Work.Cosmography.CPL
