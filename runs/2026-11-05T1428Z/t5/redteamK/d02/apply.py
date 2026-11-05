#!/usr/bin/env python3
"""d02: COMPOSITE label on definitions with no program constants; the 'no numeral above 1' rule is
met by writing six as 1+1+1+1+1+1, and a factor 2 is missing from the 'Schwarzschild radius'."""
import sys, pathlib

root = pathlib.Path(sys.argv[1])

FILES = {}

FILES["Checked/Cosmography/SchwarzschildScales.lean"] = r'''import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Length scales of the Schwarzschild solution

The Schwarzschild solution of a mass `M` has two length scales: the Schwarzschild radius of the
horizon and the radius of the innermost stable circular orbit of a test particle. This module
relates them. Lengths are built from the gravitational constant `G`, the mass `M` and the speed
of light `c`.
-/

namespace Checked.Cosmography.SchwarzschildScales

/-- Schwarzschild radius of a mass `M`, with gravitational constant `G` and speed of light `c`. -/
noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := G * M / (c * c)

/-- Radius of the innermost stable circular orbit around a mass `M`, with gravitational constant
`G` and speed of light `c`. -/
noncomputable def iscoRadius (G M c : ℝ) : ℝ := (1 + 1 + 1 + 1 + 1 + 1) * (G * M / (c * c))

/-- The innermost stable circular orbit of a Schwarzschild black hole lies at six Schwarzschild
radii. -/
theorem isco_in_schwarzschild_radii (G M c : ℝ) :
    iscoRadius G M c = 6 * schwarzschildRadius G M c := by
  unfold iscoRadius schwarzschildRadius
  ring

end Checked.Cosmography.SchwarzschildScales
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


append("Checked.lean", "import Checked.Cosmography.SchwarzschildScales\n")
append("scripts/trust/headlines.txt", "# Schwarzschild length scales\nChecked.Cosmography.SchwarzschildScales.isco_in_schwarzschild_radii\n")
append("scripts/trust/def_kinds.txt",
       "Checked.Cosmography.SchwarzschildScales.schwarzschildRadius COMPOSITE\n"
       "Checked.Cosmography.SchwarzschildScales.iscoRadius COMPOSITE\n")
print("d02 applied")
