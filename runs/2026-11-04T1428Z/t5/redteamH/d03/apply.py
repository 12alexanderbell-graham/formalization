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

LEAN = 'import Checked.Chemistry.Coexistence\nimport Checked.Trust.NonVacuity\n\n/-!\n# Reduced saturation pressure of the van der Waals fluid (corresponding-states note)\n\nA corollary of `vdW_coexistence_unique`, phrased in terms of the law of corresponding states.\n-/\n\nnamespace Checked.Chemistry.CoexistenceCorresponding\nopen Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence\n\n/-- Law of corresponding states for the van der Waals saturation pressure: every Maxwell\ncoexistence state of the van der Waals fluid with liquid volume above the co-volume b has reduced\nsaturation pressure p_s / P_c = 0.20046 to five decimals, the same number for every fluid (every\na, b, R) and at every temperature on the coexistence curve, because the van der Waals equation is\na one-parameter law in the reduced variables; the temperature written as 0.7 · 8a/(27Rb) below is\none point of that curve. -/\ntheorem vdW_saturation_corresponding (R a b vl vg ps : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)\n    (hl : b < vl)\n    (h : IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps) :\n    RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5 := by\n  exact Checked.Chemistry.Coexistence.vdW_coexistence_unique R a b vl vg ps hR ha hb hl h\n\nend Checked.Chemistry.CoexistenceCorresponding\n\nnamespace Checked.Trust.NV\n\ntheorem vdW_saturation_corresponding :\n    nonvacuity% Checked.Chemistry.CoexistenceCorresponding.vdW_saturation_corresponding := by\n  obtain ⟨vl, vg, ps, hl, h, -⟩ :=\n    Checked.Chemistry.Coexistence.vdW_coexistence_exists 1 1 1 one_pos one_pos one_pos\n  exact ⟨1, 1, 1, vl, vg, ps, one_pos, one_pos, one_pos, hl, h, trivial⟩\n\nend Checked.Trust.NV\n'
path = root / 'Checked/Chemistry/CoexistenceCorresponding.lean'
assert not path.exists()
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Chemistry.CoexistenceCorresponding\n")
append("scripts/trust/headlines.txt", '# van der Waals saturation, corresponding states (run 2026-11-04T1428Z)\nChecked.Chemistry.CoexistenceCorresponding.vdW_saturation_corresponding\n')
