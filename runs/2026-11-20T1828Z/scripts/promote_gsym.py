#!/usr/bin/env python3
"""Promote the three Work modules of the symmetry-free Gelfand bound to Checked (run 2026-11-20T1828Z).
Only namespaces, imports and module docs change; every proof is copied as written."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
MODS = ["GMaxPrinciple", "GRadialPoisson", "GSymFree"]
DOCS = {
 "GMaxPrinciple": ("/-!\n# Weak maximum principle for superharmonic functions on the unit ball of ℝ³\n",
   "/-!\n# Weak maximum principle for superharmonic functions on the unit ball of ℝ³ (`GMaxPrinciple`)\n"),
 "GSymFree": ("then `λ ≤ 3.321992119`. We remove the symmetry hypothesis of",
   "then λ is at most the bound printed in the statement of\n`Checked.Math.GelfandPDE.gelfand_pde_radial_bound`. We remove the symmetry hypothesis of"),
}
for m in MODS:
    s = (ROOT / f"Work/Math/{m}.lean").read_text()
    for a in MODS:
        s = s.replace(f"Work.Math.{a}", f"Checked.Math.{a}")
    if m in DOCS:
        old, new = DOCS[m]
        assert s.count(old) == 1, (m, old)
        s = s.replace(old, new)
    # first module doc gains the provenance sentence
    i = s.index("/-!"); j = s.index("-/", i)
    s = s[:j].rstrip() + f" Promoted from `Work/Math/{m}.lean`.\n-/" + s[j+2:]
    assert "Work." not in s, m
    (ROOT / f"Checked/Math/{m}.lean").write_text(s)
    print("wrote", m)
