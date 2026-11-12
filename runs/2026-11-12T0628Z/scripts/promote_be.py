#!/usr/bin/env python3
"""Promote the Bonnor–Ebert modules from Work/Math to Checked/Math (run 2026-11-12T0628Z; pattern of
runs/2026-11-06T1228Z/scripts/promote_g.py).

Mechanical copy: namespaces Work.Math -> Checked.Math, `import Mathlib` -> specific Mathlib modules,
`#print axioms` lines dropped, module docs replaced by number-free text (check_prose rule 7).
Statements and proofs are otherwise byte-identical to Work, except the headline docstring (says
"there is" for the existential conclusion, check_prose rule 3; the frozen Work docstring is unchanged).
"""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
W, C = ROOT / "Work/Math", ROOT / "Checked/Math"

TACTICS = ["Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring",
           "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.Positivity"]
COMMON = ["Mathlib.Analysis.SpecialFunctions.ExpDeriv", "Mathlib.Analysis.SpecialFunctions.Sqrt",
          "Mathlib.Analysis.SpecialFunctions.Exp", "Mathlib.Analysis.Real.Pi.Bounds",
          "Mathlib.Analysis.Calculus.MeanValue", "Mathlib.Analysis.Calculus.Deriv.MeanValue",
          "Mathlib.Analysis.Calculus.Deriv.Pow", "Mathlib.Analysis.Calculus.Deriv.Prod",
          "Mathlib.Analysis.Calculus.Deriv.Inv", "Mathlib.Analysis.Calculus.Deriv.Mul",
          "Mathlib.Topology.Order.IntermediateValue"] + TACTICS
GEN = "(generated certificates; promoted verbatim from `Work/Math/{f}.lean`)"
DOCS = {
    "BECellQ": "invariant modes on the exact-rational Gelfand cells: a cell certifies the sign of e^w − w'²/2 from the polynomial pe − pp²/2 and its error bound",
    "BEStart": "the singular start of the isothermal equation at a small radius, on the template of the Gelfand start",
    "BEChain": "the chain of kernel-evaluated cells from the start to the outer radius, carrying the enclosure and the sign of e^w − w'²/2",
    "BEMain": "assembly: the derivative of the pressure-confined mass is s² e^{w/2} (e^w − w'²/2)/√(4π); its unique sign change on the bracket cell, monotonicity on both sides, and the values from the enclosure and the mean value theorem",
    "BonnorEbert": "the Bonnor–Ebert critical sphere of the regular isothermal equation; bounds as printed in the statement of `bonnor_ebert_critical`",
}
FILES = ["BECellQ", "BEStart", "BEQData", "BEChain", "BEMain", "BonnorEbert"]
NEWDOC = """/-- Bonnor–Ebert critical sphere: for every S ≥ 7 and every solution w of w'' + (2/s)w' + e^w = 0 on
(0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous at 0, there is a radius
ξ₁ between 6.4507514 and 6.4507515 such that the dimensionless mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π)
increases strictly on [0, ξ₁] and decreases strictly on [ξ₁, 7]; at ξ₁ the mass lies between 1.1822265 and
1.1822266 and the centre-to-edge density contrast e^{−w(ξ₁)} between 14.042032 and 14.042033. -/
"""
for f in FILES:
    s = (W / f"{f}.lean").read_text(encoding="utf-8")
    s = s.replace("Work.Math.", "Checked.Math.")
    if "import Mathlib\n" in s:
        s = s.replace("import Mathlib\n", "".join(f"import {m}\n" for m in COMMON), 1)
    doc = DOCS.get(f, GEN.format(f=f))
    s = re.sub(r"/-!.*?-/", lambda m: f"/-! Bonnor–Ebert sphere, `{f}`: {doc}. Promoted from `Work/Math/{f}.lean`. -/", s, count=1, flags=re.S)
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    if f == "BonnorEbert":
        old = s[s.index("/-- Bonnor–Ebert critical sphere"):s.index("theorem bonnor_ebert_critical")]
        s = s.replace(old, NEWDOC)
    assert "import Mathlib\n" not in s and "Work." not in s, f
    (C / f"{f}.lean").write_text(s, encoding="utf-8")
    print("wrote", f)
