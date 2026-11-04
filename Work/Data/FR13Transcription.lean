import Work.Data.FR13
import Work.Data.FR13Table2

/-!
# Second reading of Farooq & Ratra 2013 Table 1 (trust track T3)

`Work.Data.FR13Table2` is a blind second transcription of Table 1 (a Sonnet subagent reading its
own 200 dpi render of arXiv:1301.5243v1 page 4; it saw neither the program's transcription
nor any Work/Checked file), copied verbatim. Agreement of the two readings, entry by entry:
-/

namespace Work.Data.FR13Transcription

theorem fr13Table_second_reading :
    Work.Data.FR13.fr13Table = SecondReading.FR13.fr13Table := by
  funext i
  fin_cases i <;> rfl

end Work.Data.FR13Transcription
