import Checked.Trust.SecondReadingClaimsA
import Checked.Records.Findings

/-!
# Two independent transcriptions agree: the printed formulas evaluated by the records (trust track T3,
run 2026-11-08T0628Z)

`Checked.Records.printedAvilesL0` and `printedCLSL0` name the printed formulas that the records
`F1_printedL0`, `F2_toy`, `F2_error` evaluate (before this run: a free formula and a `local notation`),
so that the role of each certified number (a value of a printed formula, of a program quantity, or a
difference of the two) is read from Lean by `scripts/trust/check_numbers.py` (rules R1–R4). Their second
readings are the blind readers' transcriptions of the same printed equations, written in run
2026-11-05T2028Z for the CLAIM definitions `AvilesL0Claim`, `CLSL0Claim` (`SecondReadingClaimsA.lean`).
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Records.printedAvilesL0` agrees with the blind second reading. -/
theorem agree_printedAvilesL0 :
    Checked.Records.printedAvilesL0 = Checked.Trust.SecondReading.avilesL0 := rfl

/-- `Checked.Records.printedCLSL0` agrees with the blind second reading. -/
theorem agree_printedCLSL0 :
    Checked.Records.printedCLSL0 = Checked.Trust.SecondReading.clsL0 := rfl

end Checked.Trust.Transcriptions
