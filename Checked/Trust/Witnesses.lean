import Checked.Trust.NonVacuity
import Checked.Sim.Duffing
import Checked.Sim.MichaelisMenten
import Checked.Sim.Robertson
import Checked.Sim.RobLong
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
import Checked.Cosmography.B1Truncation
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Checked.Cosmography.B1SepWitness
import Checked.Cosmography.B1FitWitness
import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1L19
import Checked.Data.FR13
import Checked.Chemistry.RKAcentric
import Checked.Chemistry.PRAcentric
import Checked.Chemistry.PR78Acentric
import Checked.Chemistry.SRKAcentric
import Checked.Cosmography.B1L19Curved
import Checked.Math.LaneEmden
import Checked.Math.LaneEmden2
import Checked.Math.LE2Exists
import Checked.Math.LEExists
import Checked.Math.Gelfand
import Checked.Math.GelfandExists
import Checked.Math.ThomasFermi
import Checked.Math.ThomasFermiExists
import Checked.Math.GelfandPDE
import Checked.Math.GelfandPDEExists
import Checked.Townes.TownesShooting
import Checked.Townes.TownesSolutions
import Checked.Blasius.Blasius
import Checked.Blasius.BlasiusExists
import Checked.Hiemenz.Hiemenz
import Checked.Hiemenz.HIVP
import Checked.Homann.Homann
import Checked.Homann.HmIVP
import Checked.FalknerSkan.FalknerSkan
import Checked.FalknerSkan.MonotoneWindow
import Checked.FalknerSkan.MonotoneExists
import Checked.FalknerSkan.Bounded
import Checked.FalknerSkan.HalfBounded
import Checked.FalknerSkan.FifthBounded
import Checked.FalknerSkan.Limit
import Checked.Data.Moresco16Min

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

/-! ### B1 (run 2026-10-31T0428Z): the exact global ΛCDM solution `a = sinh(3t/2)^{2/3}`,
`Ω = 1/5`, with sources at z = 3 and z = 7 (`Checked.Cosmography.B1.exists_flatLCDM_on`). -/

theorem lumDistFlat_flatLCDM : nonvacuity% Checked.Cosmography.B1.lumDistFlat_flatLCDM := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH0, hH, -, -⟩ :=
    Checked.Cosmography.B1.exists_flatLCDM_on
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₀, le_trans h73 h30, hpos, hdiff, hH0, hH, trivial⟩

theorem cubic_misses_z3 : nonvacuity% Checked.Cosmography.B1.cubic_misses_z3 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH0, hH, hz3, -⟩ :=
    Checked.Cosmography.B1.exists_flatLCDM_on
  have hsub : Set.Icc t₃ t₀ ⊆ Set.Icc t₇ t₀ := Set.Icc_subset_Icc_left h73
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₀, h30, fun s hs => hpos s (hsub hs),
    fun s hs => hdiff s (hsub hs), hH0, fun s hs => hH s (hsub hs), hz3, trivial⟩

theorem cubic_misses_z7 : nonvacuity% Checked.Cosmography.B1.cubic_misses_z7 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH0, hH, -, hz7⟩ :=
    Checked.Cosmography.B1.exists_flatLCDM_on
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₀, le_trans h73 h30, hpos, hdiff, hH0, hH, hz7,
    trivial⟩

theorem cubic_shape_miss : nonvacuity% Checked.Cosmography.B1.cubic_shape_miss := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH0, hH, hz3, hz7⟩ :=
    Checked.Cosmography.B1.exists_flatLCDM_on
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH0, hH, hz3, hz7,
    trivial⟩

/-! ### Chemistry (run 2026-10-31T0628Z): cubic equations of state. Critical points from
`exists_unique_critical` (R = a = b = 1); van der Waals explicitly (T = 8/27, v = 3). -/

theorem isCritical_iff : nonvacuity% Checked.Chemistry.CubicEOS.isCritical_iff := by
  refine ⟨1, 1, 1, 0, 0, 8 / 27, 3, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [Checked.Chemistry.CubicEOS.isCritical_iff 1 1 1 0 0 (8 / 27) 3 (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

theorem critCubic_existsUnique : nonvacuity% Checked.Chemistry.CubicEOS.critCubic_existsUnique :=
  ⟨0, 0, by norm_num, by norm_num, trivial⟩

theorem exists_unique_critical : nonvacuity% Checked.Chemistry.CubicEOS.exists_unique_critical :=
  ⟨1, 1, 1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem vdW_constants : nonvacuity% Checked.Chemistry.CubicEOS.vdW_constants := by
  refine ⟨1, 1, 1, 8 / 27, 3, by norm_num, by norm_num, by norm_num, ?_, trivial⟩
  rw [Checked.Chemistry.CubicEOS.isCritical_iff 1 1 1 0 0 (8 / 27) 3 (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

theorem rk_constants : nonvacuity% Checked.Chemistry.CubicEOS.rk_constants := by
  obtain ⟨⟨T, v⟩, ⟨_, hv, hc⟩, -⟩ := Checked.Chemistry.CubicEOS.exists_unique_critical 1 1 1 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨1, 1, 1, T, v, by norm_num, by norm_num, hv, hc, trivial⟩

theorem pr_constants : nonvacuity% Checked.Chemistry.CubicEOS.pr_constants := by
  obtain ⟨⟨T, v⟩, ⟨_, hv, hc⟩, -⟩ := Checked.Chemistry.CubicEOS.exists_unique_critical 1 1 1 2 (-1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨1, 1, 1, T, v, by norm_num, by norm_num, hv, hc, trivial⟩

/-! ### Chemistry (run 2026-11-04T0028Z): van der Waals coexistence at 0.7 T_c. `R = a = b = 1`;
the coexistence state of the uniqueness theorem is the one `vdW_coexistence_exists` provides. -/

theorem vdW_coexistence_exists : nonvacuity% Checked.Chemistry.Coexistence.vdW_coexistence_exists :=
  ⟨1, 1, 1, one_pos, one_pos, one_pos, trivial⟩

theorem vdW_coexistence_unique : nonvacuity% Checked.Chemistry.Coexistence.vdW_coexistence_unique := by
  obtain ⟨vl, vg, ps, hl, h, -⟩ :=
    Checked.Chemistry.Coexistence.vdW_coexistence_exists 1 1 1 one_pos one_pos one_pos
  exact ⟨1, 1, 1, vl, vg, ps, one_pos, one_pos, one_pos, hl, h, trivial⟩

/-! ### B1 separation/direction (run 2026-10-31T0828Z): exact ΛCDM at `Ω = 1/5` and the cubic
`a₂ = 0, a₃ = 147/25, H = 1` (`Checked.Cosmography.B1SepWitness.hyps_satisfiable`). -/

theorem cubic_separation : nonvacuity% Checked.Cosmography.B1Sep.cubic_separation := by
  obtain ⟨Ω, a, t₇, t₃, t₀, a₂, a₃, H, c, h1, h2, h73, h30, hpos, hdiff, hH0, hH, hz3, hz7, hHp,
    hp3, hp7, hm3, hm7⟩ := Checked.Cosmography.B1SepWitness.hyps_satisfiable
  exact ⟨Ω, h1, h2, a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH0, hH, hz3, hz7, a₂, a₃, H, c, hHp,
    hp3, hp7, hm3, hm7, trivial⟩

theorem cubic_direction : nonvacuity% Checked.Cosmography.B1Sep.cubic_direction := by
  obtain ⟨Ω, a, t₇, t₃, t₀, a₂, a₃, H, c, h1, h2, h73, h30, hpos, hdiff, hH0, hH, hz3, hz7, hHp,
    hp3, hp7, hm3, hm7⟩ := Checked.Cosmography.B1SepWitness.hyps_satisfiable
  exact ⟨Ω, h1, h2, a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH0, hH, hz3, hz7, a₂, a₃, H, c, hHp,
    hp3, hp7, hm3, hm7, trivial⟩

/-! ### B1 fit level (run 2026-11-04T0228Z): exact ΛCDM at `Ω = 1/5` reaching `1 + z = √2, 2√2, 4√2`
and the cubic `a₂ = 7/4, a₃ = 25/4, H = 1` (`Checked.Cosmography.B1FitWitness.hyps_satisfiable`). -/

theorem fit_direction : nonvacuity% Checked.Cosmography.B1Fit.fit_direction := by
  obtain ⟨Ω, a, t₅, t₃, t₁, t₀, a₂, a₃, H, c, h0, h1, h53, h31, h10, hpos, hdiff, hH0, hH, hz1, hz3,
    hz5, hHp, hp1, hp3, hp5, hm1, hm3, hm5⟩ := Checked.Cosmography.B1FitWitness.hyps_satisfiable
  exact ⟨Ω, h0, h1, a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH0, hH, hz1, hz3, hz5, a₂, a₃,
    H, c, hHp, hp1, hp3, hp5, hm1, hm3, hm5, trivial⟩

theorem rl19_box_unmatched : nonvacuity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched := by
  obtain ⟨Ω, a, t₅, t₃, t₁, t₀, a₂, a₃, H, h0, h1, h53, h31, h10, hpos, hdiff, hH0, hH, hz1, hz3,
    hz5, h2, h3, hHp, hp1, hp3, hp5⟩ := Checked.Cosmography.B1FitRL19.hyps_satisfiable
  exact ⟨Ω, h0, h1, a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH0, hH, hz1, hz3, hz5, a₂, a₃,
    H, 0, h2.1, h2.2, h3.1, h3.2, hHp, hp1, hp3, hp5, trivial⟩

/-! ### B1 fourth order (run 2026-11-04T1228Z): exact ΛCDM at `Ω = 1/5` reaching `1 + z = 2√2, 4√2`,
`H = 1`, and (box theorems) the quartic `a₂ = 31/10, a₃ = 4, a₄ = −2`
(`Checked.Cosmography.B1L19.hyps_satisfiable_central`, `hyps_satisfiable_box`). -/

theorem l19_sq_central : nonvacuity% Checked.Cosmography.B1L19.l19_sq_central := by
  obtain ⟨Ω, a, t₅, t₃, t₀, H, h0, h1, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, hHp⟩ :=
    Checked.Cosmography.B1L19.hyps_satisfiable_central
  exact ⟨Ω, h0, h1, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, H, hHp, trivial⟩

theorem l19_sqg_central : nonvacuity% Checked.Cosmography.B1L19.l19_sqg_central := by
  obtain ⟨Ω, a, t₅, t₃, t₀, H, h0, h1, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, hHp⟩ :=
    Checked.Cosmography.B1L19.hyps_satisfiable_central
  exact ⟨Ω, h0, h1, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, H, hHp, trivial⟩

theorem l19_sq_box : nonvacuity% Checked.Cosmography.B1L19.l19_sq_box := by
  obtain ⟨Ω, a, t₅, t₃, t₀, a₂, a₃, a₄, H, h0, h1, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, hHp,
    h2, h3, h4, hp5⟩ := Checked.Cosmography.B1L19.hyps_satisfiable_box
  exact ⟨Ω, h0, h1, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, a₂, a₃, a₄, H, hHp,
    le_trans (by norm_num) h2, le_trans h3 (by norm_num), h4, hp5, trivial⟩

theorem l19_sqg_box : nonvacuity% Checked.Cosmography.B1L19.l19_sqg_box := by
  obtain ⟨Ω, a, t₅, t₃, t₀, a₂, a₃, a₄, H, h0, h1, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, hHp,
    h2, h3, h4, hp5⟩ := Checked.Cosmography.B1L19.hyps_satisfiable_box
  exact ⟨Ω, h0, h1, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, a₂, a₃, a₄, H, hHp,
    h2, h3, le_trans h4 (by norm_num), hp5, trivial⟩

/-! ### B1 with curvature (run 2026-11-04T2028Z): the flat member `K = 0` (`Ω₀ = 1`) of the closed/flat
family, exact ΛCDM at `Ω = 1/5` (`Checked.Cosmography.B1FitWitness.exists_model`), `H = 1`. -/

lemma l19_curved_witness : ∃ (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ), t₅ ≤ t₃ ∧ t₃ ≤ t₀ ∧
    (∀ s ∈ Set.Icc t₅ t₀, 0 < a s) ∧ (∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s) ∧
    0 < Checked.Cosmography.hubble a t₀ ∧
    1 ≤ Checked.Cosmography.BambaK.omega0 0 a t₀ ∧ Checked.Cosmography.BambaK.omega0 0 a t₀ ≤ 11 / 10 ∧
    (∀ s ∈ Set.Icc t₅ t₀,
      Checked.Cosmography.hubble a s = Checked.Cosmography.hubble a t₀ *
        √(1 / 5 * (1 + Checked.Cosmography.redshift a t₀ s) ^ 3
        + (1 - Checked.Cosmography.BambaK.omega0 0 a t₀) * (1 + Checked.Cosmography.redshift a t₀ s) ^ 2
        + Checked.Cosmography.BambaK.omega0 0 a t₀ - 1 / 5)) ∧
    Checked.Cosmography.redshift a t₀ t₃ = 2 * √2 - 1 ∧
    Checked.Cosmography.redshift a t₀ t₅ = 4 * √2 - 1 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, _, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  have hω : Checked.Cosmography.BambaK.omega0 0 a t₀ = 1 := by
    simp [Checked.Cosmography.BambaK.omega0]
  refine ⟨a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀, by rw [hω], by rw [hω]; norm_num,
    fun s hs => ?_, hz₃, hz₅⟩
  rw [hω, hH s hs]
  congr 2
  ring

theorem l19_sq_curved : nonvacuity% Checked.Cosmography.B1L19Curved.l19_sq_curved := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hK0, hK1, hH, hz3, hz5⟩ := l19_curved_witness
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hK0, hK1,
    hH, hz3, hz5, 1, one_pos, trivial⟩

theorem l19_sqg_curved : nonvacuity% Checked.Cosmography.B1L19Curved.l19_sqg_curved := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hK0, hK1, hH, hz3, hz5⟩ := l19_curved_witness
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hK0, hK1,
    hH, hz3, hz5, 1, one_pos, trivial⟩

/-! ### Rigorous simulation (run 2026-11-04T0628Z): the Duffing solution from
`Checked.Sim.Duffing.duffing_solution_exists` (Picard–Lindelöf, clamped Hamiltonian field). -/

theorem duffing_first_zero_sol : nonvacuity% Checked.Sim.Duffing.duffing_first_zero_sol := by
  obtain ⟨x, hx⟩ := Checked.Sim.Duffing.duffing_solution_exists
  exact ⟨x, hx, 0, ⟨le_rfl, by norm_num⟩, trivial⟩

/-! ### Rigorous simulation of a reaction network (run 2026-11-04T0828Z): the Michaelis–Menten
solution from `Checked.Sim.MichaelisMenten.mm_solution_exists` (Picard–Lindelöf for the clamped
field; the enclosure keeps it in the box where the clamp is inactive). -/

theorem mm_half_conversion : nonvacuity% Checked.Sim.MichaelisMenten.mm_half_conversion := by
  obtain ⟨s, e, c, p, h⟩ := Checked.Sim.MichaelisMenten.mm_solution_exists
  exact ⟨s, e, c, p, h, 0, ⟨le_rfl, by norm_num⟩, trivial⟩

/-! ### Rigorous simulation of a stiff network (run 2026-11-06T0428Z, promoted 0628Z): the Robertson
solution from `Checked.Sim.Robertson.rob_exists` (Picard–Lindelöf for the clamped field; the one-sided
enclosure keeps it in the box where the clamp is inactive). -/

theorem rob_state40 : nonvacuity% Checked.Sim.Robertson.rob_state40 := by
  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.Robertson.rob_exists
  exact ⟨y₁, y₂, y₃, h, trivial⟩

/-! Robertson at t = 10¹¹ (run 2026-11-06T0828Z, promoted 1028Z): the solution from
`Checked.Sim.RobLong.rob_exists_1e11`. -/

theorem rob_state1e11 : nonvacuity% Checked.Sim.RobLong.rob_state1e11 := by
  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.RobLong.rob_exists_1e11
  exact ⟨y₁, y₂, y₃, h, trivial⟩

theorem rob_printed_y3_low : nonvacuity% Checked.Sim.RobLong.rob_printed_y3_low := by
  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.RobLong.rob_exists_1e11
  exact ⟨y₁, y₂, y₃, h, trivial⟩


/-! ### Data claim FR13 (run 2026-11-04T1628Z): a minimiser exists (`fr13_exists68`, `fr13_exists738`);
the transition equation has the solution z = (2(1 − Ω)/Ω)^(1/3) − 1 at it (Ω > 0 by the best-fit
interval). -/

theorem fr13_cube (x : ℝ) (hx : 0 < x) : ∃ z : ℝ, -1 < z ∧ (1 + z) ^ 3 = x := by
  refine ⟨x ^ ((1 : ℝ) / 3) - 1, by have := Real.rpow_pos_of_pos hx ((1 : ℝ) / 3); linarith, ?_⟩
  rw [add_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

theorem fr13_bestfit68 : nonvacuity% Checked.Data.FR13.fr13_bestfit68 := by
  obtain ⟨Ω, hΩ, h⟩ := Checked.Data.FR13.fr13_exists68
  exact ⟨Ω, hΩ.1, hΩ.2, h, trivial⟩

theorem fr13_bestfit738 : nonvacuity% Checked.Data.FR13.fr13_bestfit738 := by
  obtain ⟨Ω, hΩ, h⟩ := Checked.Data.FR13.fr13_exists738
  exact ⟨Ω, hΩ.1, hΩ.2, h, trivial⟩

theorem fr13_minval68 : nonvacuity% Checked.Data.FR13.fr13_minval68 := by
  obtain ⟨Ω, hΩ, h⟩ := Checked.Data.FR13.fr13_exists68
  exact ⟨Ω, hΩ.1, hΩ.2, h, trivial⟩

theorem fr13_minval738 : nonvacuity% Checked.Data.FR13.fr13_minval738 := by
  obtain ⟨Ω, hΩ, h⟩ := Checked.Data.FR13.fr13_exists738
  exact ⟨Ω, hΩ.1, hΩ.2, h, trivial⟩

theorem fr13_zda68 : nonvacuity% Checked.Data.FR13.fr13_zda68 := by
  obtain ⟨Ω, hΩ, h⟩ := Checked.Data.FR13.fr13_exists68
  have hb := Checked.Data.FR13.fr13_bestfit68 Ω hΩ.1 hΩ.2 h
  have hp : 0 < Ω := by linarith [hb.1]
  obtain ⟨z, hz, hc⟩ := fr13_cube (2 * (1 - Ω) / Ω) (div_pos (by linarith [hb.2]) hp)
  exact ⟨Ω, hΩ.1, hΩ.2, h, z, hz, by rw [hc]; field_simp, trivial⟩

theorem fr13_zda738 : nonvacuity% Checked.Data.FR13.fr13_zda738 := by
  obtain ⟨Ω, hΩ, h⟩ := Checked.Data.FR13.fr13_exists738
  have hb := Checked.Data.FR13.fr13_bestfit738 Ω hΩ.1 hΩ.2 h
  have hp : 0 < Ω := by linarith [hb.1]
  obtain ⟨z, hz, hc⟩ := fr13_cube (2 * (1 - Ω) / Ω) (div_pos (by linarith [hb.2]) hp)
  exact ⟨Ω, hΩ.1, hΩ.2, h, z, hz, by rw [hc]; field_simp, trivial⟩

/-! ### RK acentric factor (run 2026-11-04T1828Z): the Redlich–Kwong critical point of R = b = 1
with constant attraction 1 (`Checked.Chemistry.CubicEOS.exists_unique_critical`, u = 1, w = 0),
read as A = √T_c, so that A/√T_c = 1; the coexistence state of the uniqueness theorem is the one
`rk_coexistence_exists` provides. -/

theorem rk_crit_witness : ∃ Tc vc : ℝ, 0 < Tc ∧ 1 < vc ∧
    Checked.Chemistry.CubicEOS.IsCriticalIsotherm
      (Checked.Chemistry.CubicEOS.cubicP 1 (Real.sqrt Tc / Real.sqrt Tc) 1 1 0 Tc) vc := by
  obtain ⟨⟨Tc, vc⟩, ⟨hT, hv, hc⟩, -⟩ := Checked.Chemistry.CubicEOS.exists_unique_critical
    1 1 1 1 0 one_pos one_pos one_pos (by norm_num) (by norm_num)
  refine ⟨Tc, vc, hT, hv, ?_⟩
  rw [div_self (Real.sqrt_pos.2 hT).ne']
  exact hc

theorem rk_coexistence_exists : nonvacuity% Checked.Chemistry.RKAcentric.rk_coexistence_exists := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := rk_crit_witness
  exact ⟨1, Real.sqrt Tc, 1, Tc, vc, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, hv, hc, trivial⟩

theorem rk_coexistence_unique : nonvacuity% Checked.Chemistry.RKAcentric.rk_coexistence_unique := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := rk_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -⟩ := Checked.Chemistry.RKAcentric.rk_coexistence_exists
    1 (Real.sqrt Tc) 1 Tc vc one_pos (Real.sqrt_pos.2 hT) one_pos hT hv hc
  exact ⟨1, Real.sqrt Tc, 1, Tc, vc, vl, vg, ps, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, hv, hc,
    hl, h, trivial⟩

/-! ### Peng–Robinson at ω = 1 (run 2026-11-05T1228Z): the PR critical point of R = b = 1 with
attraction 1 at T_c (`Checked.Chemistry.CubicEOS.exists_unique_critical`, u = 2, w = −1); the
coexistence state of the uniqueness theorem is the one `pr_omega1_exists` provides. -/

theorem pr_crit_witness : ∃ Tc vc : ℝ, 0 < Tc ∧ 1 < vc ∧
    Checked.Chemistry.CubicEOS.IsCriticalIsotherm
      (Checked.Chemistry.CubicEOS.cubicP 1 1 1 2 (-1) Tc) vc := by
  obtain ⟨⟨Tc, vc⟩, ⟨hT, hv, hc⟩, -⟩ := Checked.Chemistry.CubicEOS.exists_unique_critical
    1 1 1 2 (-1) one_pos one_pos one_pos (by norm_num) (by norm_num)
  exact ⟨Tc, vc, hT, hv, hc⟩

theorem pr_omega1_exists : nonvacuity% Checked.Chemistry.PRAcentric.pr_omega1_exists := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := pr_crit_witness
  exact ⟨1, 1, 1, Tc, vc, one_pos, one_pos, hv, hc, trivial⟩

theorem pr_omega1_unique : nonvacuity% Checked.Chemistry.PRAcentric.pr_omega1_unique := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := pr_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -⟩ := Checked.Chemistry.PRAcentric.pr_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  exact ⟨1, 1, 1, Tc, vc, vl, vg, ps, one_pos, one_pos, hv, hc, hl, h, trivial⟩

-- Peng–Robinson with the revised (1978) κ at ω = 1 (run 2026-11-05T1828Z): the same critical
-- point `pr_crit_witness`; the coexistence state of the uniqueness theorem is the one
-- `pr78_omega1_exists` provides.

theorem pr78_omega1_exists : nonvacuity% Checked.Chemistry.PR78Acentric.pr78_omega1_exists := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := pr_crit_witness
  exact ⟨1, 1, 1, Tc, vc, one_pos, one_pos, hv, hc, trivial⟩

theorem pr78_omega1_unique : nonvacuity% Checked.Chemistry.PR78Acentric.pr78_omega1_unique := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := pr_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -⟩ := Checked.Chemistry.PR78Acentric.pr78_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  exact ⟨1, 1, 1, Tc, vc, vl, vg, ps, one_pos, one_pos, hv, hc, hl, h, trivial⟩

/-! ### Soave–Redlich–Kwong with Soave's κ at ω = 1 (run 2026-11-06T0028Z): the Redlich–Kwong critical
point of R = b = 1 with attraction 1 at T_c (`Checked.Chemistry.CubicEOS.exists_unique_critical`,
u = 1, w = 0); the coexistence state of the uniqueness theorem is the one `srk_omega1_exists`
provides. -/

theorem srk_crit_witness : ∃ Tc vc : ℝ, 0 < Tc ∧ 1 < vc ∧
    Checked.Chemistry.CubicEOS.IsCriticalIsotherm
      (Checked.Chemistry.CubicEOS.cubicP 1 1 1 1 0 Tc) vc := by
  obtain ⟨⟨Tc, vc⟩, ⟨hT, hv, hc⟩, -⟩ := Checked.Chemistry.CubicEOS.exists_unique_critical
    1 1 1 1 0 one_pos one_pos one_pos (by norm_num) (by norm_num)
  exact ⟨Tc, vc, hT, hv, hc⟩

theorem srk_omega1_exists : nonvacuity% Checked.Chemistry.SRKAcentric.srk_omega1_exists := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := srk_crit_witness
  exact ⟨1, 1, 1, Tc, vc, one_pos, one_pos, hv, hc, trivial⟩

theorem srk_omega1_unique : nonvacuity% Checked.Chemistry.SRKAcentric.srk_omega1_unique := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := srk_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -⟩ := Checked.Chemistry.SRKAcentric.srk_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  exact ⟨1, 1, 1, Tc, vc, vl, vg, ps, one_pos, one_pos, hv, hc, hl, h, trivial⟩

/-! ### Lane–Emden index three (run 2026-11-05T0228Z): the solution regular at the centre
constructed in `Checked.Math.LEExists.exists_solution` (Banach fixed point of the Volterra map at
the centre, Picard–Lindelöf after, glued). -/

theorem laneEmden3_constants : nonvacuity% Checked.Math.LaneEmden.laneEmden3_constants := by
  obtain ⟨θ, φ, hθ, hφ0, hφ, h0⟩ := Checked.Math.LEExists.exists_solution
  exact ⟨θ, φ, hθ, hφ0, hφ, h0, trivial⟩

/-! Lane–Emden equation of index two (run 2026-11-08T0228Z): the solution on the claim's range
constructed in `Checked.Math.LE2Exists.exists_solution` (fixed point at the centre, Picard–Lindelöf
for the clamped field after, clamps inactive by the certified cells, glued). -/

theorem laneEmden2_constants : nonvacuity% Checked.Math.LaneEmden2.laneEmden2_constants := by
  obtain ⟨θ, φ, hθ, hφ0, hφ, h0⟩ := Checked.Math.LE2Exists.exists_solution
  exact ⟨θ, φ, hθ, hφ0, hφ, h0, trivial⟩

/-! Gelfand problem in the three-dimensional ball (run 2026-11-06T1228Z, promoted 1428Z): the radial
solution on [0, S] with S = 41/10 constructed in `Checked.Math.GelfandExists.exists_solution`; the
existence headline itself at S = 1/2. -/

theorem gelfand_ball_critical : nonvacuity% Checked.Math.Gelfand.gelfand_ball_critical := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.GelfandExists.exists_solution (41 / 10) (by norm_num)
  exact ⟨41 / 10, le_rfl, w, φ, hw, hφ0, hφ, h0, trivial⟩

theorem gelfand_exists_solution : nonvacuity% Checked.Math.GelfandExists.exists_solution :=
  ⟨1 / 2, le_rfl, trivial⟩

/-! Thomas–Fermi equation of the neutral atom (run 2026-11-06T1828Z, existence and promotion
2028Z): the solution constructed in `Checked.Math.ThomasFermiExists.tf_exists` (shooting in t = √x
with the supremum of the slopes whose solution goes negative). -/

theorem tf_initial_slope : nonvacuity% Checked.Math.ThomasFermi.tf_initial_slope := by
  obtain ⟨y, φ, hy, hφ, hφ0, h0, hpos, hlim⟩ := Checked.Math.ThomasFermiExists.tf_exists
  exact ⟨y, φ, hy, hφ, hφ0, h0, hpos, hlim, trivial⟩

/-! Gelfand problem in the unit ball of three-dimensional space as a PDE (run 2026-11-06T1628Z, promoted
2026-11-07T0028Z): the radial classical solution constructed in
`Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists`, taken at the largest parameter that
theorem covers, so the hypotheses of the bound hold just below the bound itself. -/

theorem gelfand_pde_radial_bound : nonvacuity% Checked.Math.GelfandPDE.gelfand_pde_radial_bound := by
  obtain ⟨u, hu, hc, hb, hrad, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 3.321992118 (by norm_num) le_rfl
  exact ⟨3.321992118, u, hu, hc, hb, hrad, hpde, trivial⟩

theorem gelfand_pde_radial_exists : nonvacuity% Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists :=
  ⟨1, by norm_num, by norm_num, trivial⟩

/-! Townes radial equation (runs 2026-11-07T0228Z and 0628Z, promoted 2026-11-07T0828Z): a solution of the
initial-value problem at the singular point from `Checked.Townes.Solutions.ivp_exists`, at the central value
each shooting headline names, on [0, 68/5]. -/

theorem townes_under : nonvacuity% Checked.Townes.Shooting.townes_under := by
  obtain ⟨θ, φ, hθ, hφ0, hφ, h0⟩ := Checked.Townes.Solutions.ivp_exists 2.2062008646
    ⟨by norm_num, by norm_num⟩ (68 / 5) (by norm_num)
  exact ⟨68 / 5, le_rfl, θ, φ, hθ, hφ0, hφ, h0, trivial⟩

theorem townes_over : nonvacuity% Checked.Townes.Shooting.townes_over := by
  obtain ⟨θ, φ, hθ, hφ0, hφ, h0⟩ := Checked.Townes.Solutions.ivp_exists 2.2062008647
    ⟨by norm_num, by norm_num⟩ (68 / 5) (by norm_num)
  exact ⟨68 / 5, le_rfl, θ, φ, hθ, hφ0, hφ, h0, trivial⟩

/-! Blasius boundary layer (run 2026-11-07T1228Z, promoted 2026-11-07T1428Z): a solution of the boundary-value
problem from `Checked.Blasius.blasius_exists`. -/

theorem blasius_wall_shear : nonvacuity% Checked.Blasius.blasius_wall_shear := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim⟩ := Checked.Blasius.blasius_exists
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, trivial⟩

/-! Hiemenz stagnation-point flow (run 2026-11-07T2028Z, promoted 2026-11-07T2228Z): the clamped flow from the
wall at the value each shooting headline names, on [0, 15/2], where the certified cells keep every clamp
inactive (`Checked/Hiemenz/HIVP.lean`). -/

theorem hiemenz_under : nonvacuity% Checked.Hiemenz.hiemenz_under := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Hiemenz.HIVP.ivp_lo
  exact ⟨15 / 2, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, hq0, trivial⟩

theorem hiemenz_over : nonvacuity% Checked.Hiemenz.hiemenz_over := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Hiemenz.HIVP.ivp_hi
  exact ⟨15 / 2, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, hq0, trivial⟩

/-! Homann axisymmetric stagnation-point flow (run 2026-11-08T0428Z): the clamped flow from the wall at the
value each shooting headline names, on [0, 6], where the certified cells keep every clamp inactive
(`Checked/Homann/HmIVP.lean`). -/

theorem homann_under : nonvacuity% Checked.Homann.homann_under := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Homann.HmIVP.ivp_lo
  exact ⟨6, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, hq0, trivial⟩

theorem homann_over : nonvacuity% Checked.Homann.homann_over := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Homann.HmIVP.ivp_hi
  exact ⟨6, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, hq0, trivial⟩

/-! ### Data claims of Moresco et al. 2016 (runs 2026-11-05T0428Z, 0628Z; promoted 1028Z): the
printed AICc rows are attained by the value c of −2 ln L_max that makes them exact at N = 31; the
point of `Checked.Data.Moresco16Min.chiSqOL_lt` lies in the region of the lower bound. -/

theorem table5_oL_inconsistent : nonvacuity% Checked.Data.Moresco16.table5_oL_inconsistent :=
  ⟨31, 21.41 - 2 * 3 - 2 * 3 * (3 + 1) / (31 - 3 - 1), by norm_num, le_refl _, by norm_num,
    trivial⟩

theorem table5_pw_inconsistent : nonvacuity% Checked.Data.Moresco16.table5_pw_inconsistent :=
  ⟨31, 23.99 - 2 * 4 - 2 * 4 * (4 + 1) / (31 - 4 - 1), by norm_num, le_refl _, by norm_num,
    trivial⟩

theorem table5_line_inconsistent : nonvacuity% Checked.Data.Moresco16.table5_line_inconsistent :=
  ⟨31, 32.42 - 2 * 2 - 2 * 2 * (2 + 1) / (31 - 2 - 1), by norm_num, le_refl _, by norm_num,
    trivial⟩

theorem chiSqOL_ge : nonvacuity% Checked.Data.Moresco16Min.chiSqOL_ge := by
  obtain ⟨H, m, l, a1, a2, a3, -, a5, -⟩ := Checked.Data.Moresco16Min.chiSqOL_lt
  exact ⟨H, m, l, a2, by linarith, fun i => (a5 i).le, trivial⟩

theorem table5_oL_aicc_unattainable :
    nonvacuity% Checked.Data.Moresco16Min.table5_oL_aicc_unattainable := by
  obtain ⟨H, m, l, a1, a2, a3, a4, a5, -⟩ := Checked.Data.Moresco16Min.chiSqOL_lt
  exact ⟨31, H, m, l, by norm_num, le_refl _, a2, by linarith, fun i => (a5 i).le, trivial⟩

/-! Falkner–Skan rows (run 2026-11-08T0828Z): a solution of the flat-plate problem, the Blasius solution of
`Checked.Blasius.blasius_exists` rescaled by `Checked.FalknerSkan.FSScale.scale`. -/

theorem fs_zero_wall_shear : nonvacuity% Checked.FalknerSkan.fs_zero_wall_shear := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim⟩ := Checked.Blasius.blasius_exists
  have hq' : ∀ η ∈ Set.Ici (0 : ℝ), HasDerivWithinAt q (-(1 / 2 * f η * q η) - 0 * (1 - p η ^ 2))
      (Set.Ici 0) η := fun η hη => (hq η hη).congr_deriv (by ring)
  have hc : (0 : ℝ) < Real.sqrt (1 / 2) := by positivity
  have h2 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc hf hp hq'
  exact ⟨_, _, _, A, B, fun s hs => (C s hs).congr_deriv (by rw [h2]; ring), by simp [hf0],
    by simp [hp0], Checked.FalknerSkan.FSScale.scale_lim hc hlim, trivial⟩

/-! Hiemenz and Homann monotone solutions (run 2026-11-08T1028Z): the solution with positive second
derivative of `Checked.FalknerSkan.MonotoneExists.hiemenz_exists_monotone` (resp. Homann). -/

theorem hiemenz_monotone_window : nonvacuity% Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, -⟩ :=
    Checked.FalknerSkan.MonotoneExists.hiemenz_exists_monotone
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, trivial⟩

theorem homann_monotone_window : nonvacuity% Checked.FalknerSkan.MonotoneWindow.homann_monotone_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, -⟩ :=
    Checked.FalknerSkan.MonotoneExists.homann_exists_monotone
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, trivial⟩

/-! Hiemenz and Homann bounded class (run 2026-11-08T1228Z): the solution of
`Checked.FalknerSkan.Bounded.hiemenz_exists_bounded` (resp. Homann), whose velocity profile lies in
the half-open unit interval, hence between minus one and one; used twice for the uniqueness
theorems. -/

theorem hiemenz_bounded_window : nonvacuity% Checked.FalknerSkan.Bounded.hiemenz_bounded_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim,
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩, trivial⟩

theorem homann_bounded_window : nonvacuity% Checked.FalknerSkan.Bounded.homann_bounded_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.Bounded.homann_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim,
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩, trivial⟩

theorem hiemenz_bounded_equal : nonvacuity% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  have hb' : ∀ η ∈ Set.Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 :=
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hb', hf, hp, hq, hf0, hp0, hlim, hb', 0, Set.mem_Ici.2 le_rfl, trivial⟩

theorem homann_bounded_equal : nonvacuity% Checked.FalknerSkan.Bounded.homann_bounded_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.Bounded.homann_exists_bounded
  have hb' : ∀ η ∈ Set.Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 :=
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hb', hf, hp, hq, hf0, hp0, hlim, hb', 0, Set.mem_Ici.2 le_rfl, trivial⟩

/-! Falkner–Skan β = 1/2 bounded class (run 2026-11-08T1628Z): the solution of
`Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded`, whose velocity profile lies in the
half-open unit interval, hence between minus one and one; used twice for the equality theorem. -/

theorem fs_half_bounded_window : nonvacuity% Checked.FalknerSkan.HalfBounded.fs_half_bounded_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim,
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩, trivial⟩

theorem fs_half_bounded_equal : nonvacuity% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  have hb' : ∀ η ∈ Set.Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 :=
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hb', hf, hp, hq, hf0, hp0, hlim, hb', 0, Set.mem_Ici.2 le_rfl, trivial⟩

/-! Falkner–Skan β = 1/5 bounded class (run 2026-11-08T2028Z): the solution of
`Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded`, whose velocity profile lies in the
half-open unit interval, hence between minus one and one; used twice for the equality theorem. -/

theorem fs_fifth_bounded_window : nonvacuity% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim,
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩, trivial⟩

theorem fs_fifth_bounded_equal : nonvacuity% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded
  have hb' : ∀ η ∈ Set.Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 :=
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hb', hf, hp, hq, hf0, hp0, hlim, hb', 0, Set.mem_Ici.2 le_rfl, trivial⟩

/-! Falkner–Skan and stagnation-point problems with no bound on the velocity profile (run
2026-11-09T0028Z): the solutions of the existence theorems of the bounded class satisfy every
hypothesis; the coefficient one half is used for the general monotonicity theorem. -/


theorem hiemenz_limit_window : nonvacuity% Checked.FalknerSkan.Limit.hiemenz_limit_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, trivial⟩

theorem hiemenz_limit_equal : nonvacuity% Checked.FalknerSkan.Limit.hiemenz_limit_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hf, hp, hq, hf0, hp0, hlim, 0, Set.mem_Ici.2 le_rfl, trivial⟩

theorem homann_limit_window : nonvacuity% Checked.FalknerSkan.Limit.homann_limit_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.Bounded.homann_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, trivial⟩

theorem homann_limit_equal : nonvacuity% Checked.FalknerSkan.Limit.homann_limit_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.Bounded.homann_exists_bounded
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hf, hp, hq, hf0, hp0, hlim, 0, Set.mem_Ici.2 le_rfl, trivial⟩

theorem fs_half_limit_window : nonvacuity% Checked.FalknerSkan.Limit.fs_half_limit_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, trivial⟩

theorem fs_half_limit_equal : nonvacuity% Checked.FalknerSkan.Limit.fs_half_limit_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hf, hp, hq, hf0, hp0, hlim, 0, Set.mem_Ici.2 le_rfl, trivial⟩

theorem fs_fifth_limit_window : nonvacuity% Checked.FalknerSkan.Limit.fs_fifth_limit_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, trivial⟩

theorem fs_fifth_limit_equal : nonvacuity% Checked.FalknerSkan.Limit.fs_fifth_limit_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, -, -⟩ :=
    Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hf, hp, hq, hf0, hp0, hlim, 0, Set.mem_Ici.2 le_rfl, trivial⟩

end Checked.Trust.NV
