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

section StaticModel
open Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.BambaY Asymptotics

/-- A nonzero Hubble rate is needed for the misprint statement on the second luminosity-distance
coefficient in y: the static model a ≡ 1 meets every other hypothesis (11 − 5q + 3q² − j = 11 with the
junk values q = j = 0), its redshift is 0 and its remainder vanishes, so the printed series is not refuted. -/
theorem printedD2y_fails_h3 : necessity% Checked.Cosmography.BambaY.printedD2y_fails 3 := by
  have hH : hubble (fun _ : ℝ => (1 : ℝ)) 0 = 0 := by simp [hubble]
  refine ⟨fun _ => 1, 0, contDiffAt_const, one_ne_zero, ?_, ?_⟩
  · simp [decel, cosmoCoeff, hH]
  · have hz : ∀ t, remainderY printedD2y (fun _ : ℝ => (1 : ℝ)) 0 t = 0 := by
      intro t; simp [remainderY, seriesY, yred, redshift, hH]
    simp only [hz]
    exact isLittleO_zero _ _

end StaticModel
end Checked.Trust.NCB
