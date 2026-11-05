import Checked.Trust.SecondReadingFR13
import Checked.Data.FR13

/-!
# Two independent transcriptions agree: Farooq & Ratra 2013, Table 1 (trust track T3, run 2026-11-05T1028Z)

The program's transcription `Checked.Data.FR13.fr13Table` and the blind second reading
`Checked.Trust.SecondReading.fr13Table` are equal entry by entry (the agreement of
`Work/Data/FR13Transcription.lean`, now in Checked).
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Data.FR13.fr13Table` agrees with the blind second reading. -/
theorem agree_fr13Table : Checked.Data.FR13.fr13Table = Checked.Trust.SecondReading.fr13Table := by
  funext i
  fin_cases i <;> norm_num [Checked.Data.FR13.fr13Table, Checked.Trust.SecondReading.fr13Table]

end Checked.Trust.Transcriptions
