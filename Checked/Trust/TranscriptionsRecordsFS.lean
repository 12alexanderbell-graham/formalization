import Checked.Trust.SecondReadingFSSepPrinted
import Checked.Trust.SecondReadingFSFazioValues
import Checked.Records.FalknerSkan

/-!
# Two independent transcriptions agree: the printed values compared by the Falkner–Skan records (trust track T3,
run 2026-11-12T1028Z)

`Checked.Records.printedFazioSeparation`, `printedFazioWall` and `printedFazioRevWall` name the values Fazio printed
that the records `F12_separation`, `F13_wall_shear`, `F14_reversed_wall_shear` compare with the solutions, so that
the role of each certified number (a difference of a printed value and a solution's quantity) is read from Lean.
Their second readings are blind readers' transcriptions from the typeset pages (runs 2026-11-11T0828Z and
2026-11-12T1028Z).
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Records.printedFazioSeparation` agrees with the blind second reading. -/
theorem agree_printedFazioSeparation :
    Checked.Records.printedFazioSeparation = Checked.Trust.SecondReading.fsSepPrintedFazio := rfl

/-- `Checked.Records.printedFazioWall` agrees with the blind second reading. -/
theorem agree_printedFazioWall :
    Checked.Records.printedFazioWall = Checked.Trust.SecondReading.fsAttPrintedWallValueFazio := rfl

/-- `Checked.Records.printedFazioRevWall` agrees with the blind second reading. -/
theorem agree_printedFazioRevWall :
    Checked.Records.printedFazioRevWall = Checked.Trust.SecondReading.fsRevPrintedWallValueFazio := rfl

end Checked.Trust.Transcriptions
