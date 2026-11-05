#!/usr/bin/env python3
import sys, pathlib

root = pathlib.Path(sys.argv[1])


def write_new(rel, text):
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


def register(module, headlines, kinds=(), group=None):
    s = (root / "Checked.lean").read_text(encoding="utf-8")
    assert ("import " + module + "\n") not in s
    append("Checked.lean", "import " + module + "\n")
    h = ("\n# " + group + "\n" if group else "") + "".join(x + "\n" for x in headlines)
    append("scripts/trust/headlines.txt", h)
    if kinds:
        append("scripts/trust/def_kinds.txt", "".join(k + "\n" for k in kinds))

LEAN = r'''import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Trust.NonVacuity

/-!
# The Boyle temperature of a van der Waals gas

The Boyle temperature is the temperature at which the second virial coefficient vanishes, that is,
the gas behaves ideally to first order in the density. For a van der Waals gas with attraction
parameter `a`, co-volume `b` and gas constant `R` it is a closed form in `a`, `b`, `R`.
-/

namespace Checked.Chemistry.BoyleTemperature

/-- `T` is a Boyle temperature of a van der Waals gas with attraction parameter `a`, co-volume `b`
and gas constant `R`: it is positive and the second virial coefficient vanishes there. -/
structure IsBoyleTemperature (a b R T : ℝ) : Prop where
  pos : 0 < T
  zero : b - 2 * a / (R * T) = 0

/-- The Boyle temperature of a van der Waals gas with attraction parameter a, co-volume b and gas
constant R is 2a/(Rb). -/
theorem vdW_boyle_temperature (a b R : ℝ) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    IsBoyleTemperature a b R (2 * a / (R * b)) := by
  refine ⟨by positivity, ?_⟩
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have hR' : R ≠ 0 := hR.ne'
  field_simp
  try ring

theorem nv_vdW_boyle_temperature :
    nonvacuity% Checked.Chemistry.BoyleTemperature.vdW_boyle_temperature :=
  ⟨1, 1, 1, one_pos, one_pos, one_pos, trivial⟩

end Checked.Chemistry.BoyleTemperature
'''

write_new('Checked/Chemistry/BoyleTemperature.lean', LEAN)
register('Checked.Chemistry.BoyleTemperature', ['Checked.Chemistry.BoyleTemperature.vdW_boyle_temperature'], ('Checked.Chemistry.BoyleTemperature.IsBoyleTemperature COMPOSITE',), 'Boyle temperature of a van der Waals gas')
