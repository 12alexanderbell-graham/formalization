import Checked.Trust.SecondFormulationM16
import Checked.Trust.TranscriptionsM16

/-!
# Blind second formulations agree: Moresco et al. 2016 fit statistics (run 2026-11-05T1028Z)

Each FORMULA definition of `Checked.Data.Moresco16` equals the definition of the same name written
blind in `Checked.Trust.SecondFormulationM16` (from name, argument roles and conventions only). The
second formulations read the independent second transcription of Table 4; the proofs rewrite the
program's table by `Checked.Trust.Transcriptions.agree_m16Table` and close each term by `ring`.
-/

namespace Checked.Trust.Formulations

/-- `Checked.Data.Moresco16.e2OL` agrees with its blind second formulation. -/
theorem agree_e2OL : @Checked.Data.Moresco16.e2OL = @Checked.Trust.SecondFormulation.e2OL := by
  funext Ωm ΩΛ z
  simp only [Checked.Data.Moresco16.e2OL, Checked.Trust.SecondFormulation.e2OL]

/-- `Checked.Data.Moresco16.chiSqOL` agrees with its blind second formulation. -/
theorem agree_chiSqOL : @Checked.Data.Moresco16.chiSqOL = @Checked.Trust.SecondFormulation.chiSqOL := by
  funext H0 Ωm ΩΛ
  simp only [Checked.Data.Moresco16.chiSqOL, Checked.Trust.SecondFormulation.chiSqOL,
    Checked.Trust.Transcriptions.agree_m16Table, agree_e2OL]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · ring

/-- `Checked.Data.Moresco16.chiSqLine` agrees with its blind second formulation. -/
theorem agree_chiSqLine : @Checked.Data.Moresco16.chiSqLine = @Checked.Trust.SecondFormulation.chiSqLine := by
  funext a b
  simp only [Checked.Data.Moresco16.chiSqLine, Checked.Trust.SecondFormulation.chiSqLine,
    Checked.Trust.Transcriptions.agree_m16Table]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · ring

end Checked.Trust.Formulations
