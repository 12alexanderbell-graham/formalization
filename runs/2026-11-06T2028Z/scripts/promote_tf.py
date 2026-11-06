#!/usr/bin/env python3
"""Promote the Thomas–Fermi modules from Work/Math to Checked/Math (run 2026-11-06T2028Z; draft for
the promotion run: registrations, NV witness, literal readings, relock and the full build are the
next run's job).

Mechanical copy: namespaces Work.Math/Work.Sim -> Checked.Math/Checked.Sim, `import Mathlib` ->
specific Mathlib modules, `#print axioms` lines dropped, module docs replaced by number-free text
(check_prose rule 7). Statements and proofs are otherwise byte-identical to Work.
"""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
W, C = ROOT / "Work/Math", ROOT / "Checked/Math"

TACTICS = ["Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring",
           "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.Positivity", "Mathlib.Tactic.IntervalCases"]
COMMON = ["Mathlib.Analysis.SpecialFunctions.Pow.Deriv", "Mathlib.Analysis.SpecialFunctions.Sqrt",
          "Mathlib.Analysis.SpecialFunctions.Pow.Continuity",
          "Mathlib.Analysis.Calculus.MeanValue", "Mathlib.Analysis.Calculus.Deriv.MeanValue",
          "Mathlib.Analysis.Calculus.Deriv.Pow", "Mathlib.Analysis.Calculus.Deriv.Prod",
          "Mathlib.Analysis.Calculus.Deriv.Inv", "Mathlib.Analysis.Calculus.Deriv.Mul",
          "Mathlib.Analysis.Calculus.LocalExtr.Basic", "Mathlib.Analysis.Calculus.FDeriv.Prod",
          "Mathlib.Analysis.ODE.Gronwall", "Mathlib.Analysis.ODE.PicardLindelof",
          "Mathlib.Analysis.ODE.ExistUnique", "Mathlib.Topology.Order.IntermediateValue",
          "Mathlib.Topology.Algebra.Order.LiminfLimsup", "Mathlib.Order.Filter.AtTopBot.Basic",
          "Mathlib.Algebra.Order.Star.Real", "Mathlib.Topology.Order.ProjIcc"] + TACTICS
DOCS = {
    "TFReduce": "reduction of the Thomas–Fermi equation to the cooperative system of w = √y and P = y' in t = √x, and the two events that contradict positivity or decay",
    "TFCell": "Kamke first-touch barriers: one cell of a strict polynomial super- or sub-solution of the cooperative system",
    "TFChain": "chaining the generated barrier cells over the whole interval for both shooting directions",
    "ThomasFermi": "the initial slope of the neutral-atom Thomas–Fermi function; bounds as printed in the statement of `tf_initial_slope`",
    "TFExBase": "the clamped field of the regular system of u = y(t²) and Φ = y'(t²) in t = √x (the power of u extended by zero below zero)",
    "TFExFlow": "Picard–Lindelöf flow of the clamped field, continuous in the initial slope; consistency of flows and backward uniqueness",
    "TFExEvents": "the two shooting events of the clamped system: u negative and Φ positive exclude each other",
    "TFExConvert": "from a positive decaying solution in t = √x back to the Thomas–Fermi equation in x",
    "TFExAssemble": "the shooting argument: the supremum of the slopes whose solution goes negative gives a positive decaying solution",
    "ThomasFermiExists": "existence of a solution meeting every hypothesis of the Thomas–Fermi slope headline",
}
GEN = "(generated certificates; promoted verbatim from `Work/Math/{f}.lean`)"
FILES = ["TFReduce", "TFCell"] + [f"TFCertsSup{i}" for i in range(1, 5)] + \
        [f"TFCertsSub{i}" for i in range(1, 6)] + ["TFChain", "ThomasFermi", "TFExBase", "TFExFlow",
        "TFExEvents", "TFExConvert", "TFExAssemble", "ThomasFermiExists"]
for f in FILES:
    s = (W / f"{f}.lean").read_text(encoding="utf-8")
    s = s.replace("Work.Math.", "Checked.Math.").replace("Work.Sim", "Checked.Sim")
    assert "import Mathlib\n" in s, f
    s = s.replace("import Mathlib\n", "".join(f"import {m}\n" for m in COMMON), 1)
    doc = DOCS.get(f, GEN.format(f=f))
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! Thomas–Fermi, `{f}`: {doc}. Promoted from `Work/Math/{f}.lean`. -/", s, count=1, flags=re.S)
    if k == 0:
        s = re.sub(r"(?m)^(namespace )", f"/-! Thomas–Fermi, `{f}`: {doc}. Promoted from `Work/Math/{f}.lean`. -/\n\n\\1", s, count=1)
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    assert "import Mathlib\n" not in s and "Work." not in s, f
    (C / f"{f}.lean").write_text(s, encoding="utf-8")
    print("wrote", f)
