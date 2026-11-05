#!/usr/bin/env python3
"""d01: van der Waals 'Boyle temperature' (really the inversion temperature) with a self-written
'second formulation' declared with `noncomputable abbrev`, which the disclosure regex of
check_formulas.py (`^(noncomputable )?def`) does not see."""
import sys, pathlib

root = pathlib.Path(sys.argv[1])

FILES = {}

FILES["Checked/Chemistry/VdWTemperatures.lean"] = r'''import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Characteristic temperatures of the van der Waals gas

The van der Waals gas with attraction parameter `a`, co-volume `b` and gas constant `R` has a
temperature `T_c` and a Boyle temperature, the temperature at which its second virial
coefficient vanishes. This module relates the two (a scaling relation of the model).
-/

namespace Checked.Chemistry.VdWTemperatures

/-- Boyle temperature of the van der Waals gas with attraction parameter `a`, co-volume `b` and
gas constant `R`. -/
noncomputable def boyleTemp (a b R : ℝ) : ℝ := 2 * a / (R * b)

/-- The temperature `T_c` of the van der Waals gas with attraction parameter `a`, co-volume `b`
and gas constant `R`. -/
noncomputable def vdwTc (a b R : ℝ) : ℝ := 8 * a / (27 * R * b)

/-- For a van der Waals gas with attraction parameter `a`, co-volume `b` and gas constant `R`,
four times the Boyle temperature equals 27 times `T_c`. -/
theorem boyle_scaling (a b R : ℝ) : 4 * boyleTemp a b R = 27 * vdwTc a b R := by
  unfold boyleTemp vdwTc
  first | ring1 | (field_simp <;> ring1)

end Checked.Chemistry.VdWTemperatures
'''

FILES["Checked/Trust/SecondFormulationVdW.lean"] = r'''import Mathlib.Data.Real.Basic

/-!
# Second formulation of the van der Waals temperatures

Written from the names and the argument roles only (attraction parameter `a`, co-volume `b`, gas
constant `R`), without the program's definitions in front of it.
-/
namespace Checked.Trust.SecondFormulation

/-- Boyle temperature of the van der Waals gas: the temperature at which the second virial
coefficient vanishes, in terms of `a`, `b` and `R`. -/
noncomputable abbrev boyleTempBlind (a b R : ℝ) : ℝ := a / (R * b) * 2

/-- The temperature `T_c` of the van der Waals gas in terms of `a`, `b` and `R`. -/
noncomputable abbrev vdwTcBlind (a b R : ℝ) : ℝ := 8 * a / (27 * R * b)

end Checked.Trust.SecondFormulation
'''

FILES["Checked/Trust/FormulationsVdW.lean"] = r'''import Checked.Chemistry.VdWTemperatures
import Checked.Trust.SecondFormulationVdW

/-!
# The second formulations agree with the van der Waals temperature definitions
-/

namespace Checked.Trust.Formulations

/-- `Checked.Chemistry.VdWTemperatures.boyleTemp` agrees with its second formulation. -/
theorem agree_boyleTemp : @Checked.Chemistry.VdWTemperatures.boyleTemp = @Checked.Trust.SecondFormulation.boyleTempBlind := by
  funext a b R
  simp only [Checked.Chemistry.VdWTemperatures.boyleTemp, Checked.Trust.SecondFormulation.boyleTempBlind] <;> ring

/-- `Checked.Chemistry.VdWTemperatures.vdwTc` agrees with its second formulation. -/
theorem agree_vdwTc : @Checked.Chemistry.VdWTemperatures.vdwTc = @Checked.Trust.SecondFormulation.vdwTcBlind := by
  funext a b R
  simp only [Checked.Chemistry.VdWTemperatures.vdwTc, Checked.Trust.SecondFormulation.vdwTcBlind] <;> ring

end Checked.Trust.Formulations
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


append("Checked.lean", "import Checked.Chemistry.VdWTemperatures\nimport Checked.Trust.SecondFormulationVdW\nimport Checked.Trust.FormulationsVdW\n")
append("scripts/trust/headlines.txt", "# Van der Waals temperatures\nChecked.Chemistry.VdWTemperatures.boyle_scaling\n")
append("scripts/trust/def_kinds.txt",
       "Checked.Chemistry.VdWTemperatures.boyleTemp FORMULA\nChecked.Chemistry.VdWTemperatures.vdwTc FORMULA\n")
print("d01 applied")
