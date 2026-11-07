#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

p = root / "README.md"
s = p.read_text(encoding="utf-8")
last = "- Results that passed the checker: `Checked/`"
assert s.count(last) == 1
if not s.endswith("\n"):
    s += "\n"
s += ("- Findings in published formulas (`FINDINGS.md`): the sign error of Bamba et al. 2012, Eq. (10.54), the "
      "y-redshift luminosity-distance coefficient D²_{L,y}, is a theorem in Lean for FLRW universes of every curvature "
      "(`Checked.Cosmography.BambaY`): flat, open and closed, not only the flat case.\n")
p.write_text(s, encoding="utf-8")

q = root / "runs/2026-10-30T0828Z/audit.md"
t = q.read_text(encoding="utf-8")
old = "- **Scope:** Lean covers the flat instance (`Ω₀ = 1`). The referee shows the sign error holds for every curvature (Milne, open-dust Mattig checks; sympy); not in Lean."
new = ("- **Scope:** Lean covers every curvature (`Ω₀` is a free parameter of the statements, not fixed to 1). "
       "The referee's Milne and open-dust Mattig checks and sympy confirm it independently.")
assert t.count(old) == 1
q.write_text(t.replace(old, new), encoding="utf-8")
