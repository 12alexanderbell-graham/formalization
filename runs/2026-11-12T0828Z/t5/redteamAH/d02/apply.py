#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
LEAN = r"""import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Trust.Witnesses
import Checked.Chemistry.CubicEOS

/-! A restatement of the critical-point theorem for the generalized cubic equation of state. Module `NecessityM2`. -/

namespace Checked.Chemistry.CubicEOSAgain
open Checked.Chemistry.CubicEOS

/-- Existence and uniqueness of the critical point of the generalized cubic equation of state, as in
`exists_unique_critical`. -/
theorem exists_unique_critical_again (R a b u w : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hu : -2 < u) (h1 : 0 < 1 + u + w) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalIsotherm (cubicP R a b u w p.1) p.2 :=
  Checked.Chemistry.CubicEOS.exists_unique_critical R a b u w hR ha hb hu h1

end Checked.Chemistry.CubicEOSAgain

namespace Checked.Trust.NCM2

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again :=
  Checked.Trust.NV.exists_unique_critical

theorem exists_unique_critical_again_h1 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 1 :=
  Checked.Trust.NCD.exists_unique_critical_h1

theorem exists_unique_critical_again_h2 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 2 :=
  Checked.Trust.NCD.exists_unique_critical_h2

theorem exists_unique_critical_again_h3 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 3 :=
  Checked.Trust.NCD.exists_unique_critical_h3

theorem exists_unique_critical_again_h4 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 4 :=
  Checked.Trust.NCD.exists_unique_critical_h4

theorem exists_unique_critical_again_h5 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 5 :=
  Checked.Trust.NCD.exists_unique_critical_h5

end Checked.Trust.NCM2
"""
mod = "NecessityM2"
(root / "Checked" / "Trust" / (mod + ".lean")).write_text(LEAN)
p = root / "Checked.lean"
s = p.read_text()
assert ("import Checked.Trust." + mod + "\n") not in s
if not s.endswith("\n"): s += "\n"
p.write_text(s + "import Checked.Trust." + mod + "\n")
h = root / "scripts" / "trust" / "headlines.txt"
s = h.read_text()
if not s.endswith("\n"): s += "\n"
assert "Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again\n" not in s
h.write_text(s + "Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again\n")
