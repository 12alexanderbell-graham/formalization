#!/usr/bin/env python3
"""Promote the Bonnor–Ebert modules from Work/Math to Checked/Math (run 2026-11-12T0427Z).

Mechanical copy: namespaces and imports Work.Math -> Checked.Math, `import Mathlib` -> specific Mathlib
modules, module docs replaced by number-free text. Statements and proofs byte-identical to Work up to the
namespace. usage: promote_be.py <repo root>
"""
import re, sys, pathlib
ROOT = pathlib.Path(sys.argv[1])
W, C = ROOT / "Work/Math", ROOT / "Checked/Math"
MATHLIB = ["Mathlib.Analysis.SpecialFunctions.ExpDeriv", "Mathlib.Analysis.SpecialFunctions.Exp",
           "Mathlib.Analysis.SpecialFunctions.Pow.Real", "Mathlib.Analysis.SpecialFunctions.Sqrt",
           "Mathlib.Analysis.Real.Pi.Bounds", "Mathlib.Analysis.Calculus.MeanValue",
           "Mathlib.Analysis.Calculus.Deriv.MeanValue", "Mathlib.Analysis.Calculus.Deriv.Pow",
           "Mathlib.Analysis.Calculus.Deriv.Mul", "Mathlib.Analysis.Calculus.Deriv.Inv",
           "Mathlib.Topology.Order.IntermediateValue", "Mathlib.Analysis.Convex.Basic",
           "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring",
           "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.Positivity"]
DOCS = {
    "BECellQ": "the validated cells of the isothermal solution with the sign of exp w minus half the square of w' as cell invariant (positive, negative or none), checked by kernel evaluation",
    "BEStart": "the singular start of the regular isothermal solution near the centre for a solution on the interval up to seven",
    "BEQData": "the validated cells of the regular isothermal solution as data, each segment decided by kernel evaluation",
    "BEChain": "the cells chained from the start: the sign of exp w minus half the square of w' on each side of the bracket of the critical radius, and the enclosure on the bracket cell",
    "BEMain": "assembly of the critical state: derivative of the mass, the unique zero of its sign function on the bracket cell, monotonicity on both sides, values at the maximum",
    "BonnorEbert": "the critical state of the pressure-confined isothermal sphere: the first maximum of the dimensionless mass, its radius, mass and centre-to-edge density contrast, as printed in the statement of `bonnor_ebert_critical`",
}
NEWDOC = """/-- Bonnor–Ebert critical sphere: for every S ≥ 7 and every solution w of w'' + (2/s)w' + e^w = 0 on
(0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous at 0, there is a radius ξ₁
between 6.4507514 and 6.4507515 such that the dimensionless mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π)
increases strictly on [0, ξ₁] and decreases strictly on [ξ₁, 7]; there the mass lies between 1.1822265 and
1.1822266 and the centre-to-edge density contrast e^{−w(ξ₁)} between 14.042032 and 14.042033. -/
"""
for f, doc in DOCS.items():
    s = (W / f"{f}.lean").read_text(encoding="utf-8")
    s = s.replace("Work.Math.", "Checked.Math.")
    if "import Mathlib\n" in s:
        s = s.replace("import Mathlib\n", "".join(f"import {m}\n" for m in MATHLIB), 1)
    s = re.sub(r"/-!.*?-/", lambda m: f"/-! Bonnor–Ebert sphere, `{f}`: {doc}. Promoted from `Work/Math/{f}.lean`. -/", s, count=1, flags=re.S)
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    if f == "BonnorEbert":
        old = s[s.index("/-- Bonnor–Ebert critical sphere:"):s.index("theorem bonnor_ebert_critical")]
        s = s.replace(old, NEWDOC)
    assert "import Mathlib\n" not in s and "Work." not in s, f
    (C / f"{f}.lean").write_text(s, encoding="utf-8")
    print("wrote", f)
