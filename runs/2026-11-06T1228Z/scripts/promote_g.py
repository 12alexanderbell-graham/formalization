#!/usr/bin/env python3
"""Promote the Gelfand modules from Work/Math to Checked/Math (run 2026-11-06T1228Z; draft for the
promotion run: registrations, NV witness, relock and the full build are the next run's job).

Mechanical copy: namespaces Work.Math/Work.Sim -> Checked.Math/Checked.Sim, `import Mathlib` ->
specific Mathlib modules, `#print axioms` lines dropped, module docs replaced by number-free text
(check_prose rule 7). Statements and proofs are otherwise byte-identical to Work, except the
headline docstring (says "there is" for the existential conclusion, check_prose rule 3; the frozen
Work docstring is unchanged).
"""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
W, C = ROOT / "Work/Math", ROOT / "Checked/Math"

TACTICS = ["Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring",
           "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.Positivity"]
COMMON = ["Mathlib.Analysis.SpecialFunctions.ExpDeriv", "Mathlib.Analysis.SpecialFunctions.Log.Deriv",
          "Mathlib.Analysis.Complex.Exponential", "Mathlib.Analysis.Calculus.MeanValue",
          "Mathlib.Analysis.Calculus.Deriv.MeanValue", "Mathlib.Analysis.Calculus.Deriv.Pow",
          "Mathlib.Analysis.Calculus.Deriv.Prod", "Mathlib.Analysis.Calculus.Deriv.Inv",
          "Mathlib.Analysis.Calculus.Deriv.Mul", "Mathlib.Analysis.ODE.Gronwall",
          "Mathlib.Analysis.ODE.PicardLindelof", "Mathlib.Analysis.ODE.ExistUnique", "Mathlib.Topology.Order.IntermediateValue",
          "Mathlib.Algebra.Order.Star.Real", "Mathlib.Analysis.LocallyConvex.AbsConvexOpen",
          "Mathlib.Analysis.InnerProductSpace.Basic", "Mathlib.Topology.Algebra.Module.ModuleTopology",
          "Mathlib.Topology.Order.ProjIcc"] + TACTICS
LEFT = ["Mathlib.Analysis.Complex.ExponentialBounds", "Mathlib.Topology.ContinuousMap.Bounded.Basic", "Mathlib.Topology.MetricSpace.Contracting",
        "Mathlib.MeasureTheory.Integral.DominatedConvergence",
        "Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus",
        "Mathlib.Analysis.SpecialFunctions.Integrals.Basic"]
IMPORTS = {f: COMMON for f in ["GStart", "GCell", "GHelp", "GFinal", "GCerts", "GExistsRight",
                               "GelfandExists", "Gelfand"]}
IMPORTS["GExistsLeft"] = LEFT + COMMON
GEN = "(generated certificates; promoted verbatim from `Work/Math/{f}.lean`)"
DOCS = {
    "GStart": "the singular start: every solution with w(0) = 0 stays near a polynomial reference whose residual is bounded by a multiple of s², by continuous induction",
    "GCell": "one validated Grönwall cell for the polynomial system E' = E φ, φ' = −(2/t) φ − E of E = exp w and φ = w'",
    "GHelp": "Taylor bounds for the exponential and the extension of positivity of 2 + s φ by monotonicity",
    "GFinal": "assembly: the energy p²/2 + Λ − 2 log Λ (p = 2 + s w', Λ = s² exp w) is non-increasing, so the first maximum of Λ is its maximum over the whole interval",
    "GExistsRight": "existence away from the centre by Picard–Lindelöf for (w, s² φ), clamps inactive by monotonicity",
    "GExistsLeft": "a solution regular at the singular point, near the centre, by the Banach fixed point of the scaled Volterra map",
    "GelfandExists": "existence of a solution meeting every hypothesis of the Gelfand headline, glued at the junction",
    "Gelfand": "the critical parameter of the Gelfand problem in the three-dimensional ball (radial branch): the maximum of s² exp w(s) over the solution's whole interval, attained near the first zero of 2 + s w'; bounds as printed in the statement of `gelfand_ball_critical`",
}
FILES = ["GStart", "GCell", "GHelp", "GFinal", "GCerts", "GCerts1", "GCerts2", "GCerts3", "GChain",
         "Gelfand", "GExistsRight", "GExistsLeft", "GelfandExists"]
NEWDOC = """/-- Gelfand problem in the three-dimensional ball, radial branch: for every S ≥ 41/10 and every
solution w of w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with
derivative φ and φ continuous at 0, there is a point s₁ between 4.071496844 and 4.071496845 at which
s² e^{w(s)} attains its maximum over [0, S], and that maximum lies between 3.321992118 and
3.321992119. -/
"""
for f in FILES:
    s = (W / f"{f}.lean").read_text(encoding="utf-8")
    s = s.replace("Work.Math.", "Checked.Math.").replace("Work.Sim", "Checked.Sim")
    if f in IMPORTS:
        assert "import Mathlib\n" in s, f
        s = s.replace("import Mathlib\n", "".join(f"import {m}\n" for m in IMPORTS[f]), 1)
    elif "import Mathlib\n" in s:
        s = s.replace("import Mathlib\n", "".join(f"import {m}\n" for m in COMMON), 1)
    doc = DOCS.get(f, GEN.format(f=f))
    s = re.sub(r"/-!.*?-/", lambda m: f"/-! Gelfand problem, `{f}`: {doc}. Promoted from `Work/Math/{f}.lean`. -/", s, count=1, flags=re.S)
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    if f == "Gelfand":
        old = s[s.index("/-- Gelfand problem in the three-dimensional ball"):s.index("theorem gelfand_ball_critical")]
        s = s.replace(old, NEWDOC)
    assert "import Mathlib\n" not in s and "Work." not in s, f
    (C / f"{f}.lean").write_text(s, encoding="utf-8")
    print("wrote", f)
