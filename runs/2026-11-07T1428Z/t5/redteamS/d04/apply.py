#!/usr/bin/env python3
"""d04: STATE.md bullet of the Gelfand PDE pair ("Promoted to Checked + AUDITED; PROVED once CI is green", both
registered Checked headlines cited, so S1 passes) rewritten to say that the nonexistence/existence dichotomy covers
classical solutions "radial or non-radial" with the Gidas-Ni-Nirenberg reduction "also machine-checked", and that
solutions exist "precisely" up to the bound. S2's NARROW deny-list has unique/exactly/only/none/settled/
regardless/'or not'/sharp/optimal/global/..., not "precisely", "non-radial", "fail to exist", "machine-checked".
Nothing in Lean covers non-radial solutions or GNN (STATE next step 5 lists GNN as open).
usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])
p = root / "STATE.md"
t = p.read_text(encoding="utf-8")
old = ("(see the Gelfand section: the PDE form with Mathlib's Laplacian; radial classical solutions exist for "
       "0 < λ ≤ 3.321992118 and not for λ > 3.321992119).")
new = ("(see the Gelfand section: the PDE form with Mathlib's Laplacian; classical solutions of the Gelfand problem in the "
       "ball, radial or non-radial (the Gidas–Ni–Nirenberg reduction to radial profiles is covered as well), exist "
       "precisely for 0 < λ ≤ 3.321992118 and fail to exist for λ > 3.321992119; the whole dichotomy is machine-checked).")
assert t.count(old) == 1, t.count(old)
p.write_text(t.replace(old, new), encoding="utf-8")
print("d04 applied")
