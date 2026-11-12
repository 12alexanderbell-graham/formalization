#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
LEAN = r"""import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Chemistry.CubicEOS

/-! The critical cubic has a single root above one; the sign condition on `u` is stated with the region and again alone. Module `NecessityM6`. -/

namespace Checked.Chemistry.CubicEOSTwice
open Checked.Chemistry.CubicEOS

/-- The critical cubic of `critCubic_existsUnique` has exactly one root above `1` when `(u, w)` lies in the
region (`-2 < u` and `0 < 1 + u + w`) and `-2 < u`. -/
theorem critCubic_existsUnique_twice (u w : ℝ) (h : -2 < u ∧ 0 < 1 + u + w) (hu : -2 < u) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 :=
  Checked.Chemistry.CubicEOS.critCubic_existsUnique u w hu h.2

end Checked.Chemistry.CubicEOSTwice

namespace Checked.Trust.NCM6

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice :=
  ⟨0, 0, ⟨by norm_num, by norm_num⟩, by norm_num, trivial⟩

theorem critCubic_existsUnique_twice_h1 :
    necessity% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 1 :=
  Checked.Trust.NCD.critCubic_existsUnique_h2

theorem critCubic_existsUnique_twice_r2 :
    dropped% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 2 :=
  fun u w h => Checked.Chemistry.CubicEOS.critCubic_existsUnique u w h.1 h.2

theorem critCubic_existsUnique_twice_p1_1 :
    dropped% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 1 1 :=
  fun u w hu h => Checked.Chemistry.CubicEOS.critCubic_existsUnique u w hu h

theorem critCubic_existsUnique_twice_p1_2 :
    necessity% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 1 2 := by
  obtain ⟨u, w, p, hn⟩ := Checked.Trust.NCD.critCubic_existsUnique_h2
  exact ⟨u, w, p, p, hn⟩

end Checked.Trust.NCM6
"""
mod = "NecessityM6"
(root / "Checked" / "Trust" / (mod + ".lean")).write_text(LEAN)
p = root / "Checked.lean"
s = p.read_text()
assert ("import Checked.Trust." + mod + "\n") not in s
if not s.endswith("\n"): s += "\n"
p.write_text(s + "import Checked.Trust." + mod + "\n")
h = root / "scripts" / "trust" / "headlines.txt"
s = h.read_text()
if not s.endswith("\n"): s += "\n"
assert "Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice\n" not in s
h.write_text(s + "Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice\n")
