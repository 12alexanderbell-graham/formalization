import Checked.Trust.SecondReadingB1
import Checked.Cosmography.B1Truncation

/-!
# Two independent transcriptions agree: B1 batch (trust track T3, run 2026-10-31T0428Z)
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Cosmography.B1.lusA2` agrees with the blind second reading. -/
theorem agree_lusA2 : Checked.Cosmography.B1.lusA2 = Checked.Trust.SecondReading.B1.lusA2 := by
  funext Ω
  simp only [Checked.Cosmography.B1.lusA2, Checked.Trust.SecondReading.B1.lusA2]

/-- `Checked.Cosmography.B1.lusA3` agrees with the blind second reading. -/
theorem agree_lusA3 : Checked.Cosmography.B1.lusA3 = Checked.Trust.SecondReading.B1.lusA3 := by
  funext Ω
  simp only [Checked.Cosmography.B1.lusA3, Checked.Trust.SecondReading.B1.lusA3]

/-- `Checked.Cosmography.B1.logPolyDL3` agrees with the blind second reading. -/
theorem agree_logPolyDL3 :
    Checked.Cosmography.B1.logPolyDL3 = Checked.Trust.SecondReading.B1.logPolyDL3 := by
  funext a₂ a₃ H₀ z
  simp only [Checked.Cosmography.B1.logPolyDL3, Checked.Trust.SecondReading.B1.logPolyDL3]
  ring

end Checked.Trust.Transcriptions
