#!/usr/bin/env python3
"""Promote the Gelfand PDE modules from Work/Math to Checked/Math (run 2026-11-07T0028Z).

Mechanical copy: namespace Work.Math -> Checked.Math, `#print axioms` lines dropped, module docs replaced
by number-free text (check_prose rule 7). The Work modules already import specific Mathlib modules.
Statements and proofs are otherwise byte-identical to Work.
"""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
W, C = ROOT / "Work/Math", ROOT / "Checked/Math"
DOCS = {
    "RadialLaplacian": "the Laplacian of a function of the norm, away from the origin, in a finite-dimensional real inner product space",
    "GContFrom": "continuation of solutions of the radial Gelfand equation from any positive start with non-positive value and slope",
    "GelfandODEBound": "from a radial solution of the Gelfand problem on the ball to the scaled initial-value problem, and the limit that bounds its parameter by the certified maximum",
    "GelfandPDE": "the Gelfand problem in the unit ball of three-dimensional space as a PDE: no radial classical solution for a parameter above the bound printed in the statement of `gelfand_pde_radial_bound`",
    "RadialC2": "a function of the norm is twice continuously differentiable at the origin when its profile's derivatives behave like those of an even function",
    "GProfile": "elementary bounds on the scaled Gelfand profile near the centre (monotonicity only)",
    "GelfandPDEExists": "the Gelfand problem in the unit ball of three-dimensional space as a PDE: a radial classical solution exists for every positive parameter up to the bound printed in the statement of `gelfand_pde_radial_exists`",
}
FILES = ["RadialLaplacian", "GContFrom", "GelfandODEBound", "GelfandPDE", "RadialC2", "GProfile", "GelfandPDEExists"]
for f in FILES:
    s = (W / f"{f}.lean").read_text(encoding="utf-8")
    s = s.replace("Work.Math.", "Checked.Math.")
    assert "import Mathlib\n" not in s, f
    doc = DOCS[f]
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! Gelfand PDE, `{f}`: {doc}. Promoted from `Work/Math/{f}.lean`. -/", s, count=1, flags=re.S)
    assert k == 1, f
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    assert "Work." not in s and "sorry" not in s, f
    (C / f"{f}.lean").write_text(s, encoding="utf-8")
    print("wrote", f)
