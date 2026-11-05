import Checked.Trust.SecondReadingM16
import Checked.Data.Moresco16

/-!
# Two independent transcriptions agree: Moresco et al. 2016, Table 4 (trust track T3, run 2026-11-05T1028Z)

The program's transcription `Checked.Data.Moresco16.m16Table` (run 2026-11-05T0428Z) and the blind
restater's own reading of the same table (`Checked.Trust.SecondReading.m16Table`, from
`Work.Data.Moresco16Blind.table4`) are equal entry by entry.
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Data.Moresco16.m16Table` agrees with the blind second reading. -/
theorem agree_m16Table : Checked.Data.Moresco16.m16Table = Checked.Trust.SecondReading.m16Table := by
  funext i
  fin_cases i <;> norm_num [Checked.Data.Moresco16.m16Table, Checked.Trust.SecondReading.m16Table]

end Checked.Trust.Transcriptions
