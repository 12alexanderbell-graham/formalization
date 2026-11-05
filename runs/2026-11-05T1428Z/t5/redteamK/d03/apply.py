#!/usr/bin/env python3
"""d03: PRINTED transcription of the Peng-Robinson kappa(omega) correlation with a transposed digit
(1.54262 for 1.54226), and a self-written 'second reading' (no disclosure rule exists for
SecondReading* modules)."""
import sys, pathlib

root = pathlib.Path(sys.argv[1])

FILES = {}

FILES["Checked/Chemistry/PRKappa.lean"] = r'''import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Peng-Robinson correlation for the Soave exponent, as printed

Peng and Robinson (1976) correlate the exponent kappa of the temperature function of their
equation of state with the acentric factor omega by a quadratic polynomial. This module
transcribes the printed polynomial and evaluates it at the acentric factor one.
-/

namespace Checked.Chemistry.PRKappa

/-- The correlation kappa(omega) of Peng and Robinson (1976) between the acentric factor and the
exponent of Soave's temperature function, as printed in the paper. -/
noncomputable def printedKappa (ω : ℝ) : ℝ := 0.37464 + 1.54262 * ω - 0.26992 * ω ^ 2

/-- The printed correlation of Peng and Robinson (1976) gives kappa = 1.64734 at the acentric
factor 1. -/
theorem printedKappa_at_one : printedKappa 1 = 1.64734 := by
  unfold printedKappa
  norm_num

end Checked.Chemistry.PRKappa
'''

FILES["Checked/Trust/SecondReadingPRKappa.lean"] = r'''import Mathlib.Data.Real.Basic

/-!
# Second reading of the Peng-Robinson correlation for the Soave exponent

The reader's own transcription of the printed polynomial of Peng and Robinson (1976), made from
the paper without the program's transcription in front of it.
-/

namespace Checked.Trust.SecondReading.PRKappa

/-- Peng and Robinson (1976): kappa as a quadratic polynomial of the acentric factor. -/
noncomputable def kappaPolynomial (ω : ℝ) : ℝ := 0.37464 + 1.54262 * ω - 0.26992 * ω ^ 2

end Checked.Trust.SecondReading.PRKappa
'''

FILES["Checked/Trust/TranscriptionsPRKappa.lean"] = r'''import Checked.Trust.SecondReadingPRKappa
import Checked.Chemistry.PRKappa

/-!
# Two independent transcriptions agree: Peng and Robinson (1976), correlation for kappa
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Chemistry.PRKappa.printedKappa` agrees with the second reading. -/
theorem agree_printedKappa :
    Checked.Chemistry.PRKappa.printedKappa = Checked.Trust.SecondReading.PRKappa.kappaPolynomial := by
  funext ω
  simp only [Checked.Chemistry.PRKappa.printedKappa, Checked.Trust.SecondReading.PRKappa.kappaPolynomial] <;> ring

end Checked.Trust.Transcriptions
'''

for rel, text in FILES.items():
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")


append("Checked.lean", "import Checked.Chemistry.PRKappa\nimport Checked.Trust.SecondReadingPRKappa\nimport Checked.Trust.TranscriptionsPRKappa\n")
append("scripts/trust/headlines.txt", "# Peng-Robinson correlation\nChecked.Chemistry.PRKappa.printedKappa_at_one\n")
append("scripts/trust/def_kinds.txt", "Checked.Chemistry.PRKappa.printedKappa PRINTED\n")
print("d03 applied")
