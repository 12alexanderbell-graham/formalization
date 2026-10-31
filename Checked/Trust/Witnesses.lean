import Checked.Trust.NonVacuity
import Checked.Cosmography.Lookback
import Checked.Cosmography.LookbackThird
import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.LCDMWitness
import Checked.Cosmography.CPLCoefficients
import Checked.Cosmography.CPLExistence
import Checked.Cosmography.CCSLookback
import Checked.Cosmography.BambaDLy
import Checked.Cosmography.CVdQ
import Checked.Cosmography.Transverse
import Checked.Cosmography.BambaCurved
import Checked.Cosmography.BambaAngular
import Checked.Cosmography.BambaZ
import Checked.Cosmography.FRCosmo
import Checked.Cosmography.FREta
import Checked.Cosmography.DemianskiZ
import Checked.Fidelity.LumDistSpec
import Checked.Fidelity.MoreSpecs
import Checked.Fidelity.Pins
import Checked.Fidelity.FriedmannLCDM
import Checked.Fidelity.RedshiftCoeffSpecs
import Checked.Fidelity.YOmegaKSpecs
import Checked.Fidelity.FlatPins
import Checked.Fidelity.FriedmannCPL
import Checked.Fidelity.FRSpecs
import Checked.Fidelity.TransverseSpec
import Checked.Records.Findings

/-!
# Non-vacuity witnesses for the headline theorems (trust track T2, run 2026-10-30T2228Z)

For every headline `h` in `scripts/trust/headlines.txt` whose statement has a hypothesis (or a
binder that is not plain data), a theorem `Checked.Trust.NV.<short name>` proves
`nonvacuity% h`: one instance in which all hypotheses of `h` hold together. The obligation is
computed from `h`'s statement by `Checked.Trust.nvObligation`; `scripts/trust/StatementDeps.lean`
recomputes it and fails CI if a headline that needs a witness has none whose statement is
syntactically that obligation.

Instances used:
* **de Sitter** `a = exp`, `t₀ = 0`: `a₀ = 1`, `H₀ = 1`, `q₀ = −1`, every `cosmoCoeff n = 1`,
  `Ω₀ = 1 + K` (all cosmographic headlines; with `K = 1` where curvature must be nonzero).
* **flat ΛCDM** at `Ω = 1/2` (`exists_flatLCDM`, `lcdm_facts`), **flat CPL** at
  `(Ω, w₀, wₐ) = (1/2, −1, 1)` (`exists_flatCPL`): the model-predicate headlines.
* **the definitions themselves** (`*_meets_spec`): every pinning theorem's specification is
  satisfiable, so no pin is vacuous; light rays are taken with emission strictly before
  observation (`t = −1 < t₀ = 0`), not at the degenerate point `t = t₀`.
* the four equivalences `program ↔ blind formulation` need one side to hold somewhere
  (an equivalence of two unsatisfiable conditions is vacuous).
-/

open Filter Topology Real
open Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.AvilesWitness
open Checked.Cosmography.CPL Checked.Cosmography.CPLExistence Checked.Cosmography.CCS
open Checked.Cosmography.BambaY Checked.Cosmography.CVdQ Checked.Cosmography.BambaK
open Checked.Cosmography.BambaA Checked.Cosmography.BambaZ Checked.Cosmography.FRCosmo
open Checked.Cosmography.FREta Checked.Cosmography.DemianskiZ Checked.Fidelity

namespace Checked.Trust.NV

/-! ## de Sitter facts -/

lemma dS_smooth (n : WithTop ℕ∞) : ContDiffAt ℝ n Real.exp 0 := Real.contDiff_exp.contDiffAt

lemma dS_a0 : Real.exp 0 ≠ 0 := (Real.exp_pos 0).ne'

lemma dS_hubble : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]

lemma dS_hubble_ne : hubble Real.exp 0 ≠ 0 := by rw [dS_hubble]; norm_num

lemma dS_decel : decel Real.exp 0 = -1 := by simp [decel, Real.deriv_exp]

lemma dS_coeff (n : ℕ) : cosmoCoeff n Real.exp 0 = 1 := by
  simp [cosmoCoeff, iteratedDeriv_eq_iterate, Real.iter_deriv_exp, dS_hubble]

lemma dS_omega0 (K : ℝ) : omega0 K Real.exp 0 = 1 + K := by simp [omega0, dS_hubble]

/-! ## Cosmographic headlines -/

theorem lookback_second_order : nonvacuity% Checked.Cosmography.lookback_second_order :=
  ⟨Real.exp, 0, Eventually.of_forall fun _ => Real.differentiableAt_exp,
    by rw [Real.deriv_exp]; exact Real.differentiableAt_exp, dS_a0, by simp [Real.deriv_exp],
    trivial⟩

theorem lookback_second_order_bigO :
    nonvacuity% Checked.Cosmography.lookback_second_order_bigO :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, by simp [Real.deriv_exp], trivial⟩

theorem flatLCDM_coeffs : nonvacuity% Aviles.flatLCDM_coeffs := by
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM (Ω := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, t₀, hL, hs, trivial⟩

theorem printedL0_false_at : nonvacuity% AvilesWitness.printedL0_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, trivial⟩

theorem printedM0_false_at : nonvacuity% AvilesWitness.printedM0_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, by norm_num, trivial⟩

theorem flatCPL_coeffs : nonvacuity% CPL.flatCPL_coeffs := by
  obtain ⟨a, hL, hs⟩ := exists_flatCPL (1 / 2) (-1) 1
  exact ⟨1 / 2, -1, 1, a, 0, hL, hs, trivial⟩

theorem printedL0_ne : nonvacuity% CPL.printedL0_ne := by
  obtain ⟨a, hL, hs⟩ := exists_flatCPL (1 / 2) (-1) 1
  exact ⟨1 / 2, -1, 1, a, 0, hL, hs, by norm_num, trivial⟩

theorem cpl_printedL0_false_at : nonvacuity% CPLExistence.printedL0_false_at :=
  ⟨1 / 2, -1, 1, by norm_num, trivial⟩

theorem exists_local_model : nonvacuity% CPLExistence.exists_local_model :=
  ⟨fun _ => 1, contDiffAt_const, trivial⟩

theorem lookback_fifth_order : nonvacuity% CCS.lookback_fifth_order :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩

theorem printedD4_fails : nonvacuity% CCS.printedD4_fails :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_decel]; norm_num, trivial⟩

theorem printedD4_fails_past : nonvacuity% CCS.printedD4_fails_past :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_decel]; norm_num, trivial⟩

theorem lumDist_y_third_order : nonvacuity% BambaY.lumDist_y_third_order :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩

theorem printedD2y_fails : nonvacuity% BambaY.printedD2y_fails :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_decel, dS_coeff]; norm_num, trivial⟩

theorem printedD2y_fails_past : nonvacuity% BambaY.printedD2y_fails_past :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_decel, dS_coeff]; norm_num, trivial⟩

theorem dQ_y_third_order : nonvacuity% CVdQ.dQ_y_third_order :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩

theorem printedQ2_fails_past : nonvacuity% CVdQ.printedQ2_fails_past :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_decel, dS_coeff]; norm_num, trivial⟩

theorem lumDist_y_fifth_order : nonvacuity% BambaK.lumDist_y_fifth_order :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩

theorem printedD3y_fails : nonvacuity% BambaK.printedD3y_fails :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_omega0, dS_decel]; norm_num,
    trivial⟩

theorem printedD3y_fails_past : nonvacuity% BambaK.printedD3y_fails_past :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_omega0, dS_decel]; norm_num,
    trivial⟩

theorem printedD4y_fails : nonvacuity% BambaK.printedD4y_fails :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_omega0, dS_decel]; norm_num,
    trivial⟩

theorem printedD4y_fails_past : nonvacuity% BambaK.printedD4y_fails_past :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_omega0, dS_decel]; norm_num,
    trivial⟩

theorem angDist_y_fifth_order : nonvacuity% BambaA.angDist_y_fifth_order :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩

theorem printedDA3_fails : nonvacuity% BambaA.printedDA3_fails :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_omega0, dS_decel]; norm_num,
    trivial⟩

theorem printedDA3_fails_past : nonvacuity% BambaA.printedDA3_fails_past :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_omega0, dS_decel]; norm_num,
    trivial⟩

theorem printedDA4_fails : nonvacuity% BambaA.printedDA4_fails :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne,
    by rw [dS_omega0, dS_decel, dS_coeff]; norm_num, trivial⟩

theorem printedDA4_fails_past : nonvacuity% BambaA.printedDA4_fails_past :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne,
    by rw [dS_omega0, dS_decel, dS_coeff]; norm_num, trivial⟩

theorem lumDist_z_fifth_order : nonvacuity% BambaZ.lumDist_z_fifth_order :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩

theorem angDist_z_fifth_order : nonvacuity% BambaZ.angDist_z_fifth_order :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩

theorem printedDL4z_fails_past : nonvacuity% BambaZ.printedDL4z_fails_past :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, one_ne_zero, trivial⟩

theorem printedDA4z_fails_past : nonvacuity% BambaZ.printedDA4z_fails_past :=
  ⟨1, Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, one_ne_zero, trivial⟩

theorem demDL4_fails_past : nonvacuity% DemianskiZ.demDL4_fails_past :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_decel]; norm_num, trivial⟩

theorem demDA4_fails_past : nonvacuity% DemianskiZ.demDA4_fails_past :=
  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, by rw [dS_coeff]; norm_num, trivial⟩

/-! ## F(R) headlines (flat ΛCDM with `F(R) = R + 2Λ`, `Ω = 1/2`) -/

theorem fR_values : nonvacuity% FRCosmo.fR_values := by
  obtain ⟨a, t₀, -, hM⟩ := exists_LCDM_model (Ω := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, _, t₀, hM, trivial⟩

theorem curv_derivs : nonvacuity% FRCosmo.curv_derivs :=
  ⟨Real.exp, 0, Real.exp_pos 0, by rw [dS_hubble]; norm_num, dS_smooth _, trivial⟩

theorem exists_LCDM_model : nonvacuity% FRCosmo.exists_LCDM_model :=
  ⟨1 / 2, by norm_num, by norm_num, trivial⟩

theorem printedF0Mul_false_at : nonvacuity% FRCosmo.printedF0Mul_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, trivial⟩

theorem printedF0_false_at : nonvacuity% FRCosmo.printedF0_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, by norm_num, trivial⟩

theorem eta_ratios : nonvacuity% FREta.eta_ratios := by
  obtain ⟨a, t₀, hM, hq, hj, hs, hl, hR⟩ := lcdm_facts (Ω := 1 / 2) (by norm_num) (by norm_num)
  have hH := hM.expanding
  refine ⟨1 / 2, a, _, t₀, hM, ?_, ?_, ?_, trivial⟩
  · rw [hR]; nlinarith [pow_pos hH 2]
  · rw [hq, hj, hs, hl]; norm_num [correctR]
  · rw [hq, hj]; norm_num

theorem eta20_hasDerivAt : nonvacuity% FREta.eta20_hasDerivAt :=
  ⟨1 / 2, by norm_num, by norm_num, trivial⟩

theorem eta30_hasDerivAt : nonvacuity% FREta.eta30_hasDerivAt :=
  ⟨1 / 2, by norm_num, by norm_num, trivial⟩

theorem printedEta20_false_at : nonvacuity% FREta.printedEta20_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, by norm_num [printedDen], by norm_num, trivial⟩

theorem printedEta30_false_at : nonvacuity% FREta.printedEta30_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, by norm_num [printedDen], by norm_num, trivial⟩

/-! ## Pinning theorems: every specification is satisfiable (by the definition it pins) and
the physical domain of the pin is nonempty -/

theorem lumDistSpec2_pins : nonvacuity% Fidelity.lumDistSpec2_pins :=
  ⟨lumDist, lumDist_meets_spec2, 0, Real.exp, 0, -1, by norm_num, fun s _ => Real.exp_pos s,
    Real.continuous_exp.continuousOn, trivial⟩

theorem hubbleSpec_pins : nonvacuity% Fidelity.hubbleSpec_pins :=
  ⟨hubble, hubble_meets_spec, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp, trivial⟩

theorem decelSpec_pins : nonvacuity% Fidelity.decelSpec_pins :=
  ⟨decel, decel_meets_spec, Real.exp, Real.exp, Real.exp 0, 0,
    Eventually.of_forall fun s => Real.hasDerivAt_exp s, Real.hasDerivAt_exp 0, Real.exp_pos 0,
    dS_a0, trivial⟩

theorem angDistSpec_pins : nonvacuity% Fidelity.angDistSpec_pins :=
  ⟨angDist, angDist_meets_spec, 0, Real.exp, 0, -1, by norm_num, fun s _ => Real.exp_pos s,
    Real.continuous_exp.continuousOn, trivial⟩

theorem flatLCDMSpec2_pins : nonvacuity% Fidelity.flatLCDMSpec2_pins :=
  ⟨IsFlatLCDM, isFlatLCDM_meets_spec2, trivial⟩

theorem redshiftCore_pins : nonvacuity% Fidelity.redshiftCore_pins :=
  ⟨redshift, redshift_meets_core, Real.exp, 0, -1,
    ⟨fun s _ => Real.exp_pos s, Real.contDiff_exp.contDiffOn⟩, trivial⟩

theorem cosmoCoeffCore_pins : nonvacuity% Fidelity.cosmoCoeffCore_pins :=
  ⟨cosmoCoeff, cosmoCoeff_meets_core, 3, Real.exp, 0,
    ⟨Real.exp_pos 0, dS_smooth _, by simp [Real.deriv_exp]⟩, trivial⟩

theorem yRedSpec_pins : nonvacuity% Fidelity.yRedSpec_pins :=
  ⟨yred, yred_meets_spec, Real.exp, 0, -1, Real.exp_pos 0, Real.exp_pos (-1), trivial⟩

theorem omega0Spec_pins : nonvacuity% Fidelity.omega0Spec_pins :=
  ⟨omega0, omega0_meets_spec, 1, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp,
    by simp [Real.deriv_exp], trivial⟩

theorem curvKSpec_pins : nonvacuity% Fidelity.curvKSpec_pins :=
  ⟨curvK, curvK_meets_spec, 1, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp,
    by simp [Real.deriv_exp], trivial⟩

theorem lumDistFlat_pins : nonvacuity% Fidelity.lumDistFlat_pins :=
  ⟨lumDist, lumDist_meets_spec2, Real.exp, 0, -1, by norm_num, fun s _ => Real.exp_pos s,
    Real.continuous_exp.continuousOn, trivial⟩

theorem comoving_pins : nonvacuity% Fidelity.comoving_pins :=
  ⟨lumDist, lumDist_meets_spec2, Real.exp, 0, -1, by norm_num, fun s _ => Real.exp_pos s,
    Real.continuous_exp.continuousOn, trivial⟩

theorem flatCPL_pins : nonvacuity% Fidelity.flatCPL_pins :=
  ⟨FriedmannCPL, fun _ _ _ _ _ => Iff.rfl, trivial⟩

theorem ricciSpec_pins : nonvacuity% Fidelity.ricciSpec_pins :=
  ⟨curv, curv_meets_spec, Real.exp, Real.exp, Real.exp, 0, Real.exp_pos 0,
    Eventually.of_forall fun s => Real.hasDerivAt_exp s, Real.hasDerivAt_exp 0, trivial⟩

theorem transverseSpec_pins : nonvacuity% Fidelity.transverseSpec_pins :=
  ⟨Checked.Cosmography.Transverse.transverse, transverse_meets_spec, trivial⟩

/-! ## Equivalences with blind formulations: the program side holds somewhere -/

theorem isFlatLCDM_iff_friedmann : nonvacuity% Fidelity.isFlatLCDM_iff_friedmann := by
  obtain ⟨a, t₀, hL, -⟩ := exists_flatLCDM (Ω := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, t₀, hL⟩

theorem isFlatCPL_iff_friedmannCPL : nonvacuity% Fidelity.isFlatCPL_iff_friedmannCPL := by
  obtain ⟨a, hL, -⟩ := exists_flatCPL (1 / 2) (-1) 1
  exact ⟨1 / 2, -1, 1, a, 0, hL⟩

theorem friedmannEq_iff_blind : nonvacuity% Fidelity.friedmannEq_iff_blind := by
  obtain ⟨a, t₀, -, hM⟩ := Checked.Cosmography.FRCosmo.exists_LCDM_model (Ω := 1 / 2)
    (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, _, t₀, t₀, hM.friedmann⟩

theorem masterEq_iff_blind : nonvacuity% Fidelity.masterEq_iff_blind := by
  obtain ⟨a, t₀, -, hM⟩ := Checked.Cosmography.FRCosmo.exists_LCDM_model (Ω := 1 / 2)
    (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, _, t₀, t₀, hM.master.self_of_nhds⟩

/-! ### Certified numbers of the findings (`Checked/Records/Findings.lean`, run 2026-10-31T0228Z) -/

theorem F1_l0 : nonvacuity% Checked.Records.F1_l0 := by
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM (Ω := 3 / 10) (by norm_num) (by norm_num)
  exact ⟨a, t₀, hL, hs, trivial⟩

theorem F2_toy : nonvacuity% Checked.Records.F2_toy := by
  obtain ⟨a, hL, hs⟩ := exists_flatCPL (245 / 1000) (-93 / 100) (-41 / 100)
  exact ⟨a, 0, hL, hs, trivial⟩

theorem F2_error : nonvacuity% Checked.Records.F2_error := by
  obtain ⟨a, hL, hs⟩ := exists_flatCPL (3 / 10) (-1) (-1 / 2)
  exact ⟨-1, a, 0, hL, hs, trivial⟩

theorem F3_D4_LCDM : nonvacuity% Checked.Records.F3_D4_LCDM := by
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM (Ω := 3 / 10) (by norm_num) (by norm_num)
  exact ⟨a, t₀, hL, hs, trivial⟩

end Checked.Trust.NV
