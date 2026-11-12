#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
LEAN = r"""import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Chemistry.CubicEOS

/-! The critical cubic has a single root above one, for parameters in the admissible region. Module `NecessityM5`. -/

namespace Checked.Chemistry.CubicEOSRegion
open Checked.Chemistry.CubicEOS

/-- For parameters `(u, w)` in the admissible region the critical cubic has exactly one root above `1`. -/
theorem critCubic_existsUnique_region (p : ℝ × ℝ)
    (h : p ∈ {q : ℝ × ℝ | -2 < q.1 ∧ 0 < 1 + q.1 + q.2}) :
    ∃! x : ℝ, 1 < x ∧ critCubic p.1 p.2 x = 0 :=
  Checked.Chemistry.CubicEOS.critCubic_existsUnique p.1 p.2 h.1 h.2

end Checked.Chemistry.CubicEOSRegion

namespace Checked.Trust.NCM5

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSRegion.critCubic_existsUnique_region :=
  ⟨(0, 1), by norm_num, trivial⟩

theorem critCubic_existsUnique_region_h1 :
    necessity% Checked.Chemistry.CubicEOSRegion.critCubic_existsUnique_region 1 := by
  obtain ⟨u, w, p, hn⟩ := Checked.Trust.NCD.critCubic_existsUnique_h2
  exact ⟨(u, w), hn⟩

end Checked.Trust.NCM5
"""
mod = "NecessityM5"
(root / "Checked" / "Trust" / (mod + ".lean")).write_text(LEAN)
p = root / "Checked.lean"
s = p.read_text()
assert ("import Checked.Trust." + mod + "\n") not in s
if not s.endswith("\n"): s += "\n"
p.write_text(s + "import Checked.Trust." + mod + "\n")
h = root / "scripts" / "trust" / "headlines.txt"
s = h.read_text()
if not s.endswith("\n"): s += "\n"
assert "Checked.Chemistry.CubicEOSRegion.critCubic_existsUnique_region\n" not in s
h.write_text(s + "Checked.Chemistry.CubicEOSRegion.critCubic_existsUnique_region\n")
