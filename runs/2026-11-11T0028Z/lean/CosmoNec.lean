import Checked.Trust.NonVacuity
import Checked.Records.Findings
import Checked.Cosmography.CPLExistence
import Checked.Cosmography.CPLCoefficients
import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.CCSLookback

open Filter Topology
namespace Checked.Trust.NV
open Checked.Cosmography Checked.Cosmography.Aviles
lemma dS_smooth (n : WithTop ℕ∞) : ContDiffAt ℝ n Real.exp 0 := Real.contDiff_exp.contDiffAt
lemma dS_hubble : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]
lemma dS_decel : decel Real.exp 0 = -1 := by simp [decel, Real.deriv_exp]
lemma dS_coeff (n : ℕ) : cosmoCoeff n Real.exp 0 = 1 := by
  simp [cosmoCoeff, iteratedDeriv_eq_iterate, Real.iter_deriv_exp, dS_hubble]
end Checked.Trust.NV
namespace Checked.Trust.NCB
section Cosmography
open Checked.Records Checked.Cosmography Checked.Cosmography.Aviles Checked.Trust.NV

/-! ### Cosmography: model laws and the printed-coefficient condition (run 2026-11-11T0028Z)

De Sitter `a = exp` (every cosmographic coefficient 1, deceleration −1) meets every smoothness
hypothesis and falsifies the coefficient formulas of a model law with a matter density it does not
have; at Ω = 1 the CPL dark-energy terms vanish, so the printed fifth coefficient is the true one. -/

/-- The flat ΛCDM law is needed for its coefficients: de Sitter has deceleration −1, not 3Ω/2 − 1 = 1/2 at Ω = 1. -/
theorem flatLCDM_coeffs_h1 : necessity% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 := by
  refine ⟨1, Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- The flat CPL law is needed for its coefficients: de Sitter has deceleration −1, not 1/2 at Ω = 1. -/
theorem flatCPL_coeffs_h1 : necessity% Checked.Cosmography.CPL.flatCPL_coeffs 1 := by
  refine ⟨1, 0, 0, Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- The flat CPL law is needed for the misprint statement: de Sitter's fifth coefficient 1 equals the
printed formula at Ω = 0, w₀ = −1, wₐ = −96/7, where (1 − Ω)(7 − Ω)wₐ = −96 ≠ 0. -/
theorem printedL0_ne_h1 : necessity% Checked.Cosmography.CPL.printedL0_ne 1 := by
  refine ⟨0, -1, -96 / 7, Real.exp, 0, dS_smooth _, by norm_num, ?_⟩
  intro h; apply h; rw [dS_coeff]; norm_num

/-- The condition (1 − Ω)(7 − Ω)wₐ ≠ 0 is needed for the misprint statement: at Ω = 1 every flat CPL
model's fifth coefficient equals the printed formula. -/
theorem printedL0_ne_h3 : necessity% Checked.Cosmography.CPL.printedL0_ne 3 := by
  obtain ⟨a, hL, hs⟩ := Checked.Cosmography.CPLExistence.exists_flatCPL 1 0 0
  refine ⟨1, 0, 0, a, 0, hL, hs, ?_⟩
  intro h; apply h
  rw [(Checked.Cosmography.CPL.flatCPL_coeffs 1 0 0 a 0 hL hs).2.2.2]; norm_num

/-- The same condition is needed for the existence of a model refuting the printed formula: at
Ω = 1 no flat CPL model does. -/
theorem cpl_printedL0_false_at_h1 : necessity% Checked.Cosmography.CPLExistence.printedL0_false_at 1 := by
  refine ⟨1, 0, 0, ?_⟩
  rintro ⟨a, hL, hs, h⟩; apply h
  rw [(Checked.Cosmography.CPL.flatCPL_coeffs 1 0 0 a 0 hL hs).2.2.2]; norm_num

/-- The ΛCDM law is needed for record F1: de Sitter's fifth coefficient is 1, which does not round to 3.115. -/
theorem F1_l0_h1 : necessity% Checked.Records.F1_l0 1 := by
  refine ⟨Real.exp, 0, dS_smooth _, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le]

/-- The CPL law is needed for record F2 (toy): de Sitter's fifth coefficient 1 does not round to 0.809. -/
theorem F2_toy_h1 : necessity% Checked.Records.F2_toy 1 := by
  refine ⟨Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩; rw [dS_coeff] at h; norm_num [RoundsTo, abs_le] at h

/-- The CPL law is needed for record F2 (error): with de Sitter and w₀ = 0 the difference is
1 − printed ≈ 1.84, which does not round to 2.345. -/
theorem F2_error_h1 : necessity% Checked.Records.F2_error 1 := by
  refine ⟨0, Real.exp, 0, dS_smooth _, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le, printedCLSL0]

/-- The ΛCDM law is needed for record F3: de Sitter's corrected D⁴ is 1/5, which does not round to 0.2153. -/
theorem F3_D4_LCDM_h1 : necessity% Checked.Records.F3_D4_LCDM 1 := by
  refine ⟨Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩
  rw [dS_decel, dS_coeff, dS_coeff, dS_coeff] at h
  norm_num [RoundsTo, abs_le, Checked.Cosmography.CCS.correctD4] at h

end Cosmography
end Checked.Trust.NCB
