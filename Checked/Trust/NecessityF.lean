import Checked.Trust.NonVacuity
import Checked.Trust.Witnesses
import Checked.Records.Findings
import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.CPLCoefficients
import Checked.Chemistry.CubicEOS
import Checked.Sim.Duffing

/-!
# Necessity of each conjunct of a bundled hypothesis (trust track T2b item 3e, run 2026-11-11T1428Z)

Blind red team AF (run 2026-11-11T0428Z) showed that a hypothesis which is a conjunction behind a program
definition is classified only as a bundle: `necessity% thm i` says that *some* part of it matters, not
that each does. The obligation `necessity% thm i j` (`Checked/Trust/NonVacuity.lean`) asks for data
meeting every other hypothesis and every other conjunct of hypothesis `i`, with the conclusion false.
`scripts/trust/StatementDeps.lean` drops `bundled i` from the trust map once every conjunct is witnessed.

Witnesses, by family:
* **Cosmography** (`IsFlatLCDM`, `IsFlatCPL` = `0 < H₀` and, near t₀, `a > 0`, `a` differentiable and the
  expansion law): the conjunct `0 < H₀` is needed because the static model `a ≡ 1` meets the law
  (`H = 0 = 0 · √…`) and every junk coefficient (`decel`, `cosmoCoeff n`, n ≥ 1) is `0`, which is not the
  claimed value; the law conjunct is needed because de Sitter (`a = exp`, `H = 1 > 0`) has coefficients
  `−1, 1, 1, …` (the hypothesis-level witnesses of run 2026-11-11T0028Z already use it). The law conjunct
  sits under `∀ᶠ t in 𝓝 t₀` and is not split further (stated in the trust map).
* **Critical point of a cubic isotherm** (`IsCriticalIsotherm p v` = `p'(v) = 0 ∧ p''(v) = 0`), at
  R = a = b = 1, v = 2: each condition alone fixes a temperature at which the other fails and the
  compressibility factor `p v / (R T)` is not the critical value (the numbers are in each docstring).
* **Duffing initial-value problem** (`x(0) = 1 ∧ ∃ v, v(0) = 0 ∧ ODE`): without `x(0) = 1` the rest
  state `x ≡ 0` solves the equation; without the equation a straight line with `x(0) = 1` is negative
  before the certified first zero.
-/

open Set Filter Topology

namespace Checked.Trust.NCF

section Cosmography
open Checked.Records Checked.Cosmography Checked.Cosmography.Aviles Checked.Trust.NV

theorem st_hubble (t : ℝ) : hubble (fun _ : ℝ => (1 : ℝ)) t = 0 := by simp [hubble]

theorem st_coeff (n : ℕ) (hn : 0 < n) (t : ℝ) : cosmoCoeff n (fun _ : ℝ => (1 : ℝ)) t = 0 := by
  simp [cosmoCoeff, st_hubble, zero_pow hn.ne']

theorem st_decel (t : ℝ) : decel (fun _ : ℝ => (1 : ℝ)) t = 0 := by simp [decel]

/-- The static model meets every expansion law of the form `H(t) = H(t₀) · g(t)` near any t₀. -/
theorem st_law (t₀ : ℝ) (g : ℝ → ℝ) :
    ∀ᶠ t in 𝓝 t₀, 0 < (fun _ : ℝ => (1 : ℝ)) t ∧ DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) t ∧
      hubble (fun _ : ℝ => (1 : ℝ)) t = hubble (fun _ : ℝ => (1 : ℝ)) t₀ * g t :=
  Eventually.of_forall fun t => ⟨one_pos, differentiableAt_const _, by simp [st_hubble]⟩

theorem dS_H_pos : 0 < hubble Real.exp 0 := by rw [dS_hubble]; norm_num

/-- `0 < H₀` is needed in flat ΛCDM's coefficients: the static model's third coefficient is 0, not 1. -/
theorem flatLCDM_coeffs_h1_1 : necessity% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 1 := by
  refine ⟨0, fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨-, h, -⟩; rw [st_coeff 3 (by norm_num)] at h; norm_num at h

/-- The ΛCDM law is needed: de Sitter (H₀ = 1 > 0) has deceleration −1, not 1/2 at Ω = 1. -/
theorem flatLCDM_coeffs_h1_2 : necessity% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 2 := by
  refine ⟨1, Real.exp, 0, dS_smooth _, dS_H_pos, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- `0 < H₀` is needed in flat CPL's coefficients: static third coefficient 0, claimed 1 at Ω = 1. -/
theorem flatCPL_coeffs_h1_1 : necessity% Checked.Cosmography.CPL.flatCPL_coeffs 1 1 := by
  refine ⟨1, 0, 0, fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨-, h, -⟩; rw [st_coeff 3 (by norm_num)] at h; norm_num at h

/-- The CPL law is needed: de Sitter has deceleration −1, not 1/2 at Ω = 1. -/
theorem flatCPL_coeffs_h1_2 : necessity% Checked.Cosmography.CPL.flatCPL_coeffs 1 2 := by
  refine ⟨1, 0, 0, Real.exp, 0, dS_smooth _, dS_H_pos, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- `0 < H₀` is needed in the misprint statement: the static fifth coefficient 0 equals the printed
formula at Ω = 0, w₀ = 0, wₐ = (−213 + √43409)/14 (a root of 7wₐ² + 213wₐ + 70 = 0, so the printed value
35/2 + (213 + 7wₐ)wₐ/4 is 0), where (1 − Ω)(7 − Ω)wₐ = 7wₐ ≠ 0. -/
theorem printedL0_ne_h1_1 : necessity% Checked.Cosmography.CPL.printedL0_ne 1 1 := by
  set w := (-213 + √43409) / 14 with hw
  have hs : √43409 ^ 2 = 43409 := Real.sq_sqrt (by norm_num)
  have hq : 7 * w ^ 2 + 213 * w + 70 = 0 := by rw [hw]; nlinarith [hs]
  have hlt : √43409 < 213 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : 0 < √43409 := Real.sqrt_pos.2 (by norm_num)
  have hw0 : w ≠ 0 := by rw [hw]; intro h; nlinarith
  refine ⟨0, 0, w, fun _ => 1, 0, contDiffAt_const, by
    simpa using hw0, st_law _ _, ?_⟩
  rw [st_coeff 5 (by norm_num)]
  intro h; apply h; linear_combination (-1 / 4 : ℝ) * hq

/-- The CPL law is needed in the misprint statement: de Sitter's fifth coefficient 1 equals the printed
formula at Ω = 0, w₀ = −1, wₐ = −96/7 (the hypothesis-level witness `printedL0_ne_h1`). -/
theorem printedL0_ne_h1_2 : necessity% Checked.Cosmography.CPL.printedL0_ne 1 2 := by
  refine ⟨0, -1, -96 / 7, Real.exp, 0, dS_smooth _, by norm_num, dS_H_pos, ?_⟩
  intro h; apply h; rw [dS_coeff]; norm_num

/-- Record F1: `0 < H₀` is needed (static fifth coefficient 0 does not round to 3.115). -/
theorem F1_l0_h1_1 : necessity% Checked.Records.F1_l0 1 1 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rw [st_coeff 5 (by norm_num)]; norm_num [RoundsTo, abs_le]

/-- Record F1: the ΛCDM law is needed (de Sitter's fifth coefficient 1 does not round to 3.115). -/
theorem F1_l0_h1_2 : necessity% Checked.Records.F1_l0 1 2 := by
  refine ⟨Real.exp, 0, dS_smooth _, dS_H_pos, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le]

/-- Record F2 (toy): `0 < H₀` is needed (static fifth coefficient 0 does not round to 0.809). -/
theorem F2_toy_h1_1 : necessity% Checked.Records.F2_toy 1 1 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨h, -⟩; rw [st_coeff 5 (by norm_num)] at h; norm_num [RoundsTo, abs_le] at h

/-- Record F2 (toy): the CPL law is needed (de Sitter: 1 does not round to 0.809). -/
theorem F2_toy_h1_2 : necessity% Checked.Records.F2_toy 1 2 := by
  refine ⟨Real.exp, 0, dS_smooth _, dS_H_pos, ?_⟩
  rintro ⟨h, -⟩; rw [dS_coeff] at h; norm_num [RoundsTo, abs_le] at h

/-- Record F2 (error): `0 < H₀` is needed (static, w₀ = 0: 0 − printed ≈ 0.84, not 2.345). -/
theorem F2_error_h1_1 : necessity% Checked.Records.F2_error 1 1 := by
  refine ⟨0, fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rw [st_coeff 5 (by norm_num)]; norm_num [RoundsTo, abs_le, printedCLSL0]

/-- Record F2 (error): the CPL law is needed (de Sitter, w₀ = 0: 1 − printed ≈ 1.84, not 2.345). -/
theorem F2_error_h1_2 : necessity% Checked.Records.F2_error 1 2 := by
  refine ⟨0, Real.exp, 0, dS_smooth _, dS_H_pos, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le, printedCLSL0]

/-- Record F3: `0 < H₀` is needed (static: every coefficient 0, corrected D⁴ = 1, not 0.2153). -/
theorem F3_D4_LCDM_h1_1 : necessity% Checked.Records.F3_D4_LCDM 1 1 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨h, -⟩
  rw [st_decel, st_coeff 3 (by norm_num), st_coeff 4 (by norm_num), st_coeff 5 (by norm_num)] at h
  norm_num [RoundsTo, abs_le, Checked.Cosmography.CCS.correctD4] at h

/-- Record F3: the ΛCDM law is needed (de Sitter's corrected D⁴ is 1/5, not 0.2153). -/
theorem F3_D4_LCDM_h1_2 : necessity% Checked.Records.F3_D4_LCDM 1 2 := by
  refine ⟨Real.exp, 0, dS_smooth _, dS_H_pos, ?_⟩
  rintro ⟨h, -⟩
  rw [dS_decel, dS_coeff, dS_coeff, dS_coeff] at h
  norm_num [RoundsTo, abs_le, Checked.Cosmography.CCS.correctD4] at h

end Cosmography

section Chemistry
open Checked.Records Checked.Chemistry.CubicEOS

/-- vdW: zero slope is needed: at T = 3/16 the curvature vanishes, the slope is 1/16, and Z = −2/3. -/
theorem vdW_constants_h4_1 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 4 1 := by
  refine ⟨1, 1, 1, 3 / 16, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [deriv2_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- vdW: zero curvature is needed: at T = 1/4 the slope vanishes and Z = 0. -/
theorem vdW_constants_h4_2 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 4 2 := by
  refine ⟨1, 1, 1, 1 / 4, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [(hasDerivAt_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)).deriv]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- RK: zero slope is needed: at T = 19/216 the curvature vanishes and Z = −34/19. -/
theorem rk_constants_h4_1 : necessity% Checked.Chemistry.CubicEOS.rk_constants 4 1 := by
  refine ⟨1, 1, 1, 19 / 216, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [deriv2_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- RK: zero curvature is needed: at T = 5/36 the slope vanishes and Z = −2/5. -/
theorem rk_constants_h4_2 : necessity% Checked.Chemistry.CubicEOS.rk_constants 4 2 := by
  refine ⟨1, 1, 1, 5 / 36, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [(hasDerivAt_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)).deriv]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- PR: zero slope is needed: at T = 29/343 the curvature vanishes and Z = −40/29. -/
theorem pr_constants_h4_1 : necessity% Checked.Chemistry.CubicEOS.pr_constants 4 1 := by
  refine ⟨1, 1, 1, 29 / 343, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [deriv2_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP, RoundsTo, abs_le] at h

/-- PR: zero curvature is needed: at T = 6/49 the slope vanishes and Z = −1/3. -/
theorem pr_constants_h4_2 : necessity% Checked.Chemistry.CubicEOS.pr_constants 4 2 := by
  refine ⟨1, 1, 1, 6 / 49, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [(hasDerivAt_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)).deriv]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP, RoundsTo, abs_le] at h

end Chemistry

section Duffing
open Checked.Sim.Duffing

/-- Duffing: the initial position is needed: the rest state x ≡ 0 solves the equation with v(0) = 0. -/
theorem duffing_first_zero_sol_h1_1 : necessity% Checked.Sim.Duffing.duffing_first_zero_sol 1 1 := by
  refine ⟨fun _ => 0, ⟨fun _ => 0, rfl, fun t _ => ⟨?_, ?_⟩⟩, ?_⟩
  · exact hasDerivWithinAt_const _ _ _
  · simpa using hasDerivWithinAt_const t (Icc (0 : ℝ) (6 / 5)) (0 : ℝ)
  · rintro ⟨h, -⟩; exact lt_irrefl _ (h 0 (by norm_num))

/-- Duffing: the equation is needed: x(t) = 1 − 2t has x(0) = 1 and is negative at t = 1. -/
theorem duffing_first_zero_sol_h1_2 : necessity% Checked.Sim.Duffing.duffing_first_zero_sol 1 2 := by
  refine ⟨fun t => 1 - 2 * t, by norm_num, ?_⟩
  rintro ⟨h, -⟩; have := h 1 (by norm_num); norm_num at this

end Duffing

end Checked.Trust.NCF
