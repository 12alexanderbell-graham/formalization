#!/usr/bin/env python3
"""Promote the Moresco et al. 2016 modules from Work/Data to Checked/Data (run 2026-11-05T1028Z).

Copies each Work module, renames the namespace Work.Data.X -> Checked.Data.X, replaces
`import Mathlib` by the specific Mathlib modules below, drops `#print axioms` lines.
Statements and proofs are copied unchanged; module docs and docstrings are rewritten by hand
afterwards where the prose rules require it (check_prose.py).
Run from the repository root.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MODS = ["Moresco16Certs", "Moresco16", "Moresco16Lower", "Moresco16MinTools",
        "Moresco16MinCerts0", "Moresco16MinCerts1", "Moresco16MinCerts2", "Moresco16MinCerts3",
        "Moresco16MinCover", "Moresco16Min"]
MATHLIB = {
    "Moresco16Certs": ["Mathlib.Analysis.SpecialFunctions.Pow.Real", "Mathlib.Analysis.Real.Sqrt",
                       "Mathlib.Data.Fin.VecNotation", "Mathlib.Algebra.BigOperators.Fin",
                       "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring",
                       "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.Positivity",
                       "Mathlib.Tactic.FinCases"],
    "Moresco16": ["Mathlib.Analysis.SpecialFunctions.Log.Basic",
                  "Mathlib.Analysis.Complex.ExponentialBounds"],
    "Moresco16MinTools": ["Mathlib.Algebra.Order.Field.Rat", "Mathlib.Data.Rat.Cast.Order"],
    "Moresco16Min": ["Mathlib.Order.ConditionallyCompleteLattice.Basic"],
}

for m in MODS:
    src = (ROOT / f"Work/Data/{m}.lean").read_text()
    lines = src.splitlines()
    out = []
    for l in lines:
        if l.strip() == "import Mathlib":
            out += [f"import {x}" for x in MATHLIB.get(m, [])]
            continue
        if l.startswith("#print axioms"):
            continue
        out.append(l)
    text = "\n".join(out).rstrip() + "\n"
    text = re.sub(r"\bWork\.Data\.(Moresco16\w*)", r"Checked.Data.\1", text)
    (ROOT / f"Checked/Data/{m}.lean").write_text(text)
    print("wrote", m)
