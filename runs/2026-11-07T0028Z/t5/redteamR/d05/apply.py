#!/usr/bin/env python3
"""d05: STATE.md "Results" bullet of the promoted Gelfand PDE pair rewritten as **PROVED** citing the two Checked
headlines, with two claims the headlines do not make (uniqueness; all solutions, not only radial ones).
usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])
p = root / "STATE.md"
text = p.read_text(encoding="utf-8")
old = ("- **PROVED in Work + AUDITED** (part 5 mathematics, run 2026-11-06T1628Z; local build, axioms standard; CI of 1757139 and 03bbb04: next run) "
       "`Work.Math.GelfandPDE.gelfand_pde_radial_bound`, `Work.Math.GelfandPDEExists.gelfand_pde_radial_exists` "
       "(see the Gelfand section: the PDE form, radial solutions exist for 0 < λ ≤ 3.321992118 and not for λ > 3.321992119).")
assert text.count(old) == 1
new = ("- **PROVED** (part 5 mathematics, runs 2026-11-06T1628Z, 2026-11-07T0028Z; promotion d32edba, local full build and every trust script green; "
       "Work proofs and blind closure green) "
       "`Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists`, `Checked.Math.GelfandPDE.gelfand_pde_radial_bound` "
       "(see the Gelfand section: the Gelfand problem Δu + λeᵘ = 0, u = 0 on the unit sphere of ℝ³, has exactly one classical solution for every "
       "0 < λ ≤ 3.321992118 and none at all for λ > 3.321992119, radial or not, so the critical parameter of the three-dimensional ball is "
       "λ* = 3.32199212 to nine digits and the thermal-explosion threshold of a sphere is settled).")
p.write_text(text.replace(old, new), encoding="utf-8")
print("d05 applied")
