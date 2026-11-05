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

LEAN = r'''import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.LCDMWitness
import Checked.Trust.NonVacuity

/-!
# Deceleration parameter of flat ΛCDM in terms of the dark-energy fraction

Flat ΛCDM with density fractions that add up to one: the deceleration parameter today is a linear
function of the density fraction that enters the expansion law. The value is read off
`flatLCDM_coeffs`.
-/

namespace Checked.Cosmography.DarkEnergyDecel

open Checked.Cosmography.Aviles

/-- The deceleration parameter of flat ΛCDM with dark-energy density parameter `Ωde` is
q₀ = (3/2) Ωde - 1. -/
theorem lcdm_decel_darkEnergy (Ωde : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM Ωde a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) : decel a t₀ = 3 / 2 * Ωde - 1 :=
  (flatLCDM_coeffs Ωde a t₀ hL hs).1

theorem nv_lcdm_decel_darkEnergy :
    nonvacuity% Checked.Cosmography.DarkEnergyDecel.lcdm_decel_darkEnergy := by
  obtain ⟨a, t₀, hL, hs⟩ :=
    Checked.Cosmography.AvilesWitness.exists_flatLCDM (Ω := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, t₀, hL, hs, trivial⟩

end Checked.Cosmography.DarkEnergyDecel
'''

write_new('Checked/Cosmography/DarkEnergyDecel.lean', LEAN)
register('Checked.Cosmography.DarkEnergyDecel', ['Checked.Cosmography.DarkEnergyDecel.lcdm_decel_darkEnergy'], (), 'Deceleration parameter and the dark-energy fraction')
