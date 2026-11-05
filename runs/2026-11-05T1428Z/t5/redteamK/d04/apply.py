#!/usr/bin/env python3
"""d04: the pinned `redshift` used outside the domain of its pin (a(t) = 0): Lean's x/0 = 0 makes
the redshift of light from the Big Bang equal to -1."""
import sys, pathlib

root = pathlib.Path(sys.argv[1])

FILES = {}

FILES["Checked/Cosmography/BigBangRedshift.lean"] = r'''import Checked.Cosmography.Lookback
import Checked.Trust.NonVacuity

/-!
# The redshift at vanishing scale factor

The redshift of light emitted at a time `t` is the ratio of the scale factors at observation and
emission, minus one. This module records its value at a time where the scale factor of the
emitter's epoch vanishes.
-/

namespace Checked.Cosmography.BigBangRedshift

/-- Light emitted at a time `t` at which the scale factor `a` is zero has redshift minus one. -/
theorem redshift_minus_one_at_zero_scale (a : ℝ → ℝ) (t₀ t : ℝ) (h : a t = 0) :
    Checked.Cosmography.redshift a t₀ t = -1 := by
  simp [Checked.Cosmography.redshift, h]

/-- A scale factor that vanishes at some time exists. -/
theorem nv_redshift_minus_one_at_zero_scale :
    nonvacuity% Checked.Cosmography.BigBangRedshift.redshift_minus_one_at_zero_scale :=
  ⟨fun _ => 0, 0, 0, by simp, trivial⟩

end Checked.Cosmography.BigBangRedshift
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


append("Checked.lean", "import Checked.Cosmography.BigBangRedshift\n")
append("scripts/trust/headlines.txt", "# Redshift at vanishing scale factor\nChecked.Cosmography.BigBangRedshift.redshift_minus_one_at_zero_scale\n")
print("d04 applied")
