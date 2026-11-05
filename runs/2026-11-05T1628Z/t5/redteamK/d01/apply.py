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

LEAN = r'''import Lean
import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.LCDMWitness
import Checked.Trust.NonVacuity

/-!
# The present deceleration parameter of flat ΛCDM stays in a band

For flat ΛCDM with matter fraction in the closed unit interval, the deceleration parameter today
lies between its value for de Sitter space and its value for Einstein-de Sitter space. The proof
reads the value off `flatLCDM_coeffs`.
-/

namespace Checked.Cosmography.LCDMDecelBand

open Checked.Cosmography.Aviles

open Lean PrettyPrinter in
/-- Short display of inequalities in printed statements. -/
@[app_unexpander LE.le]
def unexpandLEShort : Unexpander
  | `($_ $a $b) => `($a < $b)
  | _ => throw ()

/-- Flat ΛCDM with matter fraction Ω in the unit interval has its deceleration parameter q₀
between -1 and 1/2. -/
theorem lcdm_decel_band (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hΩ : Ω ∈ Set.Icc (0 : ℝ) 1)
    (hL : IsFlatLCDM Ω a t₀) (hs : ContDiffAt ℝ 6 a t₀) :
    -1 ≤ decel a t₀ ∧ decel a t₀ ≤ 1 / 2 := by
  have h := (flatLCDM_coeffs Ω a t₀ hL hs).1
  obtain ⟨h0, h1⟩ := hΩ
  constructor <;> linarith

theorem nv_lcdm_decel_band : nonvacuity% Checked.Cosmography.LCDMDecelBand.lcdm_decel_band := by
  obtain ⟨a, t₀, hL, hs⟩ :=
    Checked.Cosmography.AvilesWitness.exists_flatLCDM (Ω := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, t₀, Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩, hL, hs, trivial⟩

end Checked.Cosmography.LCDMDecelBand
'''

write_new('Checked/Cosmography/LCDMDecelBand.lean', LEAN)
register('Checked.Cosmography.LCDMDecelBand', ['Checked.Cosmography.LCDMDecelBand.lcdm_decel_band'], (), 'Deceleration band of flat LCDM')
