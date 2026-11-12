#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
LEAN = r"""import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Chemistry.CubicEOS

/-! The critical cubic has a single root above one, with the sign condition handed in as a lifted proof. Module `NecessityM4`. -/

namespace Checked.Chemistry.CubicEOSLift
open Checked.Chemistry.CubicEOS

/-- The critical cubic of `critCubic_existsUnique` has exactly one root above `1`; the positivity of
`1 + u + w` is handed in as a lifted proof `h1`. -/
theorem critCubic_existsUnique_lift (u w : ℝ) (hu : -2 < u) (h1 : PLift (0 < 1 + u + w)) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 :=
  Checked.Chemistry.CubicEOS.critCubic_existsUnique u w hu h1.down

end Checked.Chemistry.CubicEOSLift

namespace Checked.Trust.NCM4

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSLift.critCubic_existsUnique_lift :=
  ⟨0, 0, by norm_num, ⟨by norm_num⟩, trivial⟩

theorem critCubic_existsUnique_lift_h1 :
    necessity% Checked.Chemistry.CubicEOSLift.critCubic_existsUnique_lift 1 := by
  obtain ⟨u, w, p, hn⟩ := Checked.Trust.NCD.critCubic_existsUnique_h1
  exact ⟨u, w, ⟨p⟩, hn⟩

end Checked.Trust.NCM4
"""
mod = "NecessityM4"
(root / "Checked" / "Trust" / (mod + ".lean")).write_text(LEAN)
p = root / "Checked.lean"
s = p.read_text()
assert ("import Checked.Trust." + mod + "\n") not in s
if not s.endswith("\n"): s += "\n"
p.write_text(s + "import Checked.Trust." + mod + "\n")
h = root / "scripts" / "trust" / "headlines.txt"
s = h.read_text()
if not s.endswith("\n"): s += "\n"
assert "Checked.Chemistry.CubicEOSLift.critCubic_existsUnique_lift\n" not in s
h.write_text(s + "Checked.Chemistry.CubicEOSLift.critCubic_existsUnique_lift\n")
