import Checked.Trust.NonVacuity
import Checked.Cosmography.B1Fit
import Checked.Cosmography.B1FitCerts
import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1FitTools
import Checked.Cosmography.B1FitWitness
import Checked.Cosmography.B1L19
import Checked.Cosmography.B1L19Certs
import Checked.Cosmography.B1SepWitness
import Checked.Cosmography.B1Separation
import Checked.Cosmography.B1Truncation
import Checked.Cosmography.BambaAngular
import Checked.Cosmography.BambaCurved
import Checked.Cosmography.BambaDLy
import Checked.Cosmography.BambaZ
import Checked.Cosmography.CCSLookback
import Checked.Cosmography.CPLCoefficients
import Checked.Cosmography.CPLExistence
import Checked.Cosmography.CVdQ
import Checked.Cosmography.DemianskiZ
import Checked.Cosmography.FRCosmo
import Checked.Cosmography.FREta
import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.LCDMWitness
import Checked.Cosmography.Lookback
import Checked.Cosmography.LookbackThird
import Checked.Cosmography.Transverse

open Filter Topology
namespace Checked.Trust.NCB

section HubbleScale
/-! ### A nonzero scale factor is implied by a nonzero Hubble rate (run 2026-11-11T0028Z)

`hubble a t₀ = deriv a t₀ / a t₀`, and division by zero gives zero, so a nonzero Hubble rate forces a
nonzero present scale factor: the hypothesis `a t₀ ≠ 0` is redundant in every headline that also
assumes `hubble a t₀ ≠ 0`. -/

theorem ne_a0_of_hubble {a : ℝ → ℝ} {t₀ : ℝ} (h : Checked.Cosmography.hubble a t₀ ≠ 0) : a t₀ ≠ 0 :=
  fun h0 => h (by simp [Checked.Cosmography.hubble, h0])

theorem lookback_fifth_order_r2 : dropped% Checked.Cosmography.CCS.lookback_fifth_order 2 := by
  intros
  apply Checked.Cosmography.CCS.lookback_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4_fails_r2 : dropped% Checked.Cosmography.CCS.printedD4_fails 2 := by
  intros
  apply Checked.Cosmography.CCS.printedD4_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4_fails_past_r2 : dropped% Checked.Cosmography.CCS.printedD4_fails_past 2 := by
  intros
  apply Checked.Cosmography.CCS.printedD4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem lumDist_y_third_order_r2 : dropped% Checked.Cosmography.BambaY.lumDist_y_third_order 2 := by
  intros
  apply Checked.Cosmography.BambaY.lumDist_y_third_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD2y_fails_r2 : dropped% Checked.Cosmography.BambaY.printedD2y_fails 2 := by
  intros
  apply Checked.Cosmography.BambaY.printedD2y_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD2y_fails_past_r2 : dropped% Checked.Cosmography.BambaY.printedD2y_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaY.printedD2y_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem dQ_y_third_order_r2 : dropped% Checked.Cosmography.CVdQ.dQ_y_third_order 2 := by
  intros
  apply Checked.Cosmography.CVdQ.dQ_y_third_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedQ2_fails_past_r2 : dropped% Checked.Cosmography.CVdQ.printedQ2_fails_past 2 := by
  intros
  apply Checked.Cosmography.CVdQ.printedQ2_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem lumDist_y_fifth_order_r2 : dropped% Checked.Cosmography.BambaK.lumDist_y_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaK.lumDist_y_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD3y_fails_r2 : dropped% Checked.Cosmography.BambaK.printedD3y_fails 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD3y_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD3y_fails_past_r2 : dropped% Checked.Cosmography.BambaK.printedD3y_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD3y_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4y_fails_r2 : dropped% Checked.Cosmography.BambaK.printedD4y_fails 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD4y_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4y_fails_past_r2 : dropped% Checked.Cosmography.BambaK.printedD4y_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD4y_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem angDist_y_fifth_order_r2 : dropped% Checked.Cosmography.BambaA.angDist_y_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaA.angDist_y_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA3_fails_r2 : dropped% Checked.Cosmography.BambaA.printedDA3_fails 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA3_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA3_fails_past_r2 : dropped% Checked.Cosmography.BambaA.printedDA3_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA3_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA4_fails_r2 : dropped% Checked.Cosmography.BambaA.printedDA4_fails 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA4_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA4_fails_past_r2 : dropped% Checked.Cosmography.BambaA.printedDA4_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem lumDist_z_fifth_order_r2 : dropped% Checked.Cosmography.BambaZ.lumDist_z_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaZ.lumDist_z_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem angDist_z_fifth_order_r2 : dropped% Checked.Cosmography.BambaZ.angDist_z_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaZ.angDist_z_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDL4z_fails_past_r2 : dropped% Checked.Cosmography.BambaZ.printedDL4z_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaZ.printedDL4z_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA4z_fails_past_r2 : dropped% Checked.Cosmography.BambaZ.printedDA4z_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaZ.printedDA4z_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem demDL4_fails_past_r2 : dropped% Checked.Cosmography.DemianskiZ.demDL4_fails_past 2 := by
  intros
  apply Checked.Cosmography.DemianskiZ.demDL4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem demDA4_fails_past_r2 : dropped% Checked.Cosmography.DemianskiZ.demDA4_fails_past 2 := by
  intros
  apply Checked.Cosmography.DemianskiZ.demDA4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

end HubbleScale

end Checked.Trust.NCB
