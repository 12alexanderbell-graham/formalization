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

/-!
# Flat ΛCDM at the Planck 2018 matter fraction

The baseline Planck 2018 analysis fixes the matter fraction of flat ΛCDM. At that matter fraction
the present-day deceleration parameter is negative: the expansion accelerates. The value follows
from `flatLCDM_coeffs`.
-/

namespace Checked.Cosmography.Planck2018Flat

open Checked.Cosmography.Aviles Checked.Cosmography.AvilesWitness

/-- There is a flat ΛCDM model with the Planck 2018 matter fraction 0.265 whose present-day
deceleration parameter is minus 0.6025: the expansion accelerates. -/
theorem planck2018_flat_lcdm_accelerates :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM (53 / 200) a t₀ ∧ ContDiffAt ℝ 6 a t₀ ∧
      decel a t₀ = -(241 / 400) := by
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM (Ω := 53 / 200) (by norm_num) (by norm_num)
  refine ⟨a, t₀, hL, hs, ?_⟩
  rw [(flatLCDM_coeffs _ a t₀ hL hs).1]
  norm_num

end Checked.Cosmography.Planck2018Flat
'''

write_new('Checked/Cosmography/Planck2018Flat.lean', LEAN)
register('Checked.Cosmography.Planck2018Flat', ['Checked.Cosmography.Planck2018Flat.planck2018_flat_lcdm_accelerates'], (), 'Planck 2018 flat LCDM')
