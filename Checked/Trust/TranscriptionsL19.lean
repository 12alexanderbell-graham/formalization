import Checked.Trust.SecondReadingL19
import Checked.Cosmography.B1L19

/-!
# Two independent transcriptions agree: Lusso et al. 2019 Eq. (7) (trust track T3, run 2026-11-04T1228Z)
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Cosmography.B1L19.logPolyDL4` agrees with the blind second reading. -/
theorem agree_logPolyDL4 :
    Checked.Cosmography.B1L19.logPolyDL4 = Checked.Trust.SecondReading.L19.logPolyDL4 := by
  funext a₂ a₃ a₄ H₀ z
  simp only [Checked.Cosmography.B1L19.logPolyDL4, Checked.Trust.SecondReading.L19.logPolyDL4]
  ring

end Checked.Trust.Transcriptions
