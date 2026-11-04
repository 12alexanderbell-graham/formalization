#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def rep(path, old, new):
    p = root / path
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (path, old)
    p.write_text(s.replace(old, new), encoding="utf-8")

def append(path, text):
    p = root / path
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")

LEAN = "import Checked.Chemistry.Coexistence\nimport Checked.Trust.NonVacuity\n\n/-!\n# Acentric factor of the van der Waals fluid (summary of `vdW_coexistence_exists`)\n-/\n\nnamespace Checked.Chemistry.AcentricValue\nopen Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence\n\n/-- Acentric factor of the van der Waals fluid. At T = 0.7 · 8a/(27Rb) (that is 0.7 T_c) there is a\nMaxwell coexistence state (liquid volume above the co-volume b) whose pressure is 0.20046 · a/(27b²)\n(that is 0.20046 P_c) to five decimals, so Pitzer's acentric factor of the van der Waals fluid is\n0.3020 to four decimals: positive, as for every fluid whose molecules are less spherical than the\nargon-like simple-fluid reference. -/\ntheorem vdW_acentric_value (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :\n    ∃ vl vg ps, b < vl ∧\n      IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps ∧\n      RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5 ∧\n      RoundsTo (acentric ps (a / (27 * b ^ 2))) (-0.3020) 4 := by\n  exact Checked.Chemistry.Coexistence.vdW_coexistence_exists R a b hR ha hb\n\nend Checked.Chemistry.AcentricValue\n\nnamespace Checked.Trust.NV\n\ntheorem vdW_acentric_value :\n    nonvacuity% Checked.Chemistry.AcentricValue.vdW_acentric_value :=\n  ⟨1, 1, 1, one_pos, one_pos, one_pos, trivial⟩\n\nend Checked.Trust.NV\n"
path = root / 'Checked/Chemistry/AcentricValue.lean'
assert not path.exists()
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Chemistry.AcentricValue\n")
append("scripts/trust/headlines.txt", '# van der Waals acentric factor (run 2026-11-04T1428Z)\nChecked.Chemistry.AcentricValue.vdW_acentric_value\n')
