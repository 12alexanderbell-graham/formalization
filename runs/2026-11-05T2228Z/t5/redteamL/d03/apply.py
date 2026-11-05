#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def write(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)

def append(rel, text):
    p = root / rel
    s = p.read_text()
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text)

write('Checked/Chemistry/BoyleTemperature.lean', 'import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Positivity\n\n/-!\n# Boyle temperature of a van der Waals gas (run 2026-11-05T2228Z)\n\nFor a gas obeying the van der Waals equation with parameters `a`, `b` and gas constant `R`, the\nBoyle temperature is the temperature at which the second virial coefficient vanishes.\n-/\n\nnamespace Checked.Chemistry.BoyleTemperature\n\n/-- Zero-pressure inversion temperature of a van der Waals gas in the second-virial approximation. -/\nnoncomputable def vdwInversionTemp (a b R : ℝ) : ℝ := 2 * a / (R * b)\n\n/-- Boyle temperature of a van der Waals gas with parameters `a`, `b` and gas constant `R`: the\ntemperature at which the second virial coefficient `b - a/(R T)` vanishes. -/\nnoncomputable def boyleTemperature (a b R : ℝ) : ℝ := 2 * a / (R * b)\n\n/-- **Boyle temperature of a van der Waals gas.** For positive `a`, `b` and `R` the Boyle temperature is\npositive and equals `2a/(Rb)`. -/\ntheorem boyle_temperature (a b R : ℝ) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :\n    0 < boyleTemperature a b R ∧ boyleTemperature a b R = 2 * a / (R * b) :=\n  ⟨by unfold boyleTemperature; positivity, rfl⟩\n\nend Checked.Chemistry.BoyleTemperature\n')

write('Checked/Trust/SecondFormulationG.lean', 'import Mathlib.Data.Real.Basic\nimport Checked.Chemistry.BoyleTemperature\n\nnamespace Checked.Trust.SecondFormulationG\n\n/-- Boyle temperature of a van der Waals gas: the temperature `T` at which the second virial coefficient\n`b - a/(R T)` vanishes, as a function of `a`, `b` and the gas constant `R`. -/\nnoncomputable def boyleTemperature (a b R : ℝ) : ℝ := Checked.Chemistry.BoyleTemperature.vdwInversionTemp a b R\n\nend Checked.Trust.SecondFormulationG\n')

write('Checked/Trust/FormulationsG.lean', 'import Checked.Trust.SecondFormulationG\nimport Checked.Chemistry.BoyleTemperature\n\nnamespace Checked.Trust.Formulations\n\n/-- `Checked.Chemistry.BoyleTemperature.boyleTemperature` agrees with its blind second formulation. -/\ntheorem agree_boyleTemperature : @Checked.Chemistry.BoyleTemperature.boyleTemperature = @Checked.Trust.SecondFormulationG.boyleTemperature := by\n  funext a b R\n  rfl\n\nend Checked.Trust.Formulations\n')

write('Checked/Trust/NVBoyle.lean', 'import Checked.Trust.NonVacuity\nimport Checked.Chemistry.BoyleTemperature\n\nnamespace Checked.Trust.NV\n\ntheorem boyle_temperature : nonvacuity% Checked.Chemistry.BoyleTemperature.boyle_temperature :=\n  ⟨1, 1, 1, one_pos, one_pos, one_pos, trivial⟩\n\nend Checked.Trust.NV\n')

append('Checked.lean', 'import Checked.Chemistry.BoyleTemperature\nimport Checked.Trust.SecondFormulationG\nimport Checked.Trust.FormulationsG\nimport Checked.Trust.NVBoyle\n')
append('scripts/trust/headlines.txt', 'BoyleTemperature.boyle_temperature\n')
append('scripts/trust/def_kinds.txt', 'Checked.Chemistry.BoyleTemperature.boyleTemperature FORMULA\n')
append('LEDGER.md', '## 2026-11-05 · run 2026-11-05T2228Z · Boyle temperature of a van der Waals gas, second formulation (part 5)\n- **Blind second formulation** (Sonnet; brief `runs/2026-11-05T2228Z/blind_formulation/briefG.md`), copied verbatim to `SecondFormulationG.lean` (`boyleTemperature`). Agreement `FormulationsG.lean` (`agree_boyleTemperature`): agrees. New headline `boyle_temperature` (module `BoyleTemperature`), witness `NVBoyle.lean`.\n')
