#!/usr/bin/env python3
"""Promote the Hiemenz trio (hiemenz_under, hiemenz_over, hiemenz_exists) and its supporting modules from Work to
Checked (run 2026-11-07T2228Z; pattern of runs/2026-11-07T1428Z/scripts/promote_blasius.py).

Mechanical copy: `Work.` -> `Checked.` in every name (the Work import of `Work.Sim.OneSided3` becomes its Checked
copy `Checked.Sim.OneSided3`, whose code is the same), module docs replaced by number-free text (check_prose
rule 7), `#print axioms` lines dropped. Statements and proofs otherwise byte-identical to Work. `import Mathlib`
is replaced by specific modules: the import sets of the analogous Blasius modules (BExBase, BCellW, BExFlow,
BExBounds, BlasiusExists, Blasius), plus the five tactic modules.
"""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = ["Mathlib.Algebra.Order.Star.Real", "Mathlib.Analysis.LocallyConvex.AbsConvexOpen", "Mathlib.Analysis.ODE.ExistUnique"]
CELL = ["Mathlib.Algebra.Order.Star.Real", "Mathlib.Analysis.InnerProductSpace.Basic",
        "Mathlib.Analysis.LocallyConvex.AbsConvexOpen", "Mathlib.Topology.Algebra.Module.ModuleTopology",
        "Mathlib.Analysis.SpecialFunctions.ExpDeriv"]
MODS = {
    "HExBase": (BASE, "the Hiemenz field with its components clamped, globally Lipschitz, and the two shooting events (undershoot and overshoot) for a state curve"),
    "HCellW": (CELL, "validated cells of the Hiemenz system in a weighted norm with a one-sided bound certified by the Sylvester criterion, the sign conditions of the two shooting events carried along a chain, each segment from one Boolean check over the rationals decided by kernel evaluation"),
    "HCellWC": (CELL + ["Mathlib.Analysis.ODE.ExistUnique"], "the validated cells of `HCellW` for the clamped Hiemenz field, with the ball of every cell inside the clamps, so that the same certificates apply to the flow of the clamped field"),
    "HUData": (None, "the cells of the Hiemenz initial-value problem started below the wall shear, checked by kernel evaluation, ending in the undershoot event"),
    "HOData": (None, "the cells of the Hiemenz initial-value problem started above the wall shear, checked by kernel evaluation, ending in the overshoot event"),
    "HUDataC": (None, "the cells of `HUData` for the clamped field, ending in the undershoot event of the clamped flow"),
    "HODataC": (None, "the cells of `HOData` for the clamped field, ending in the overshoot event of the clamped flow"),
    "HExFlow": (BASE, "a global solution of the clamped Hiemenz system from the wall for each wall value of q, continuous in that wall value, with forward and backward uniqueness"),
    "HExLimit": (BASE, "a solution of the clamped Hiemenz system with neither shooting event is a solution of the Hiemenz boundary-value problem"),
    "HExAssemble": (BASE, "the supremum argument: a wall value between the two certified shooting values with neither event, hence a solution of the Hiemenz boundary-value problem"),
    "Hiemenz": (BASE, "the Hiemenz stagnation-point flow: the two shooting events at the ends of the wall-shear window printed in the statements of `hiemenz_under` and `hiemenz_over`, and existence of a solution of the boundary-value problem with wall shear in that window (`hiemenz_exists`); uniqueness of that solution is not formalised"),
}
TACTICS = [f"Mathlib.Tactic.{t}" for t in ("NormNum", "Linarith", "Ring", "FieldSimp", "Positivity")]


def promote(key, imports, doc):
    src = ROOT / "Work" / "Hiemenz" / f"{key}.lean"
    dst = ROOT / "Checked" / "Hiemenz" / f"{key}.lean"
    s = src.read_text(encoding="utf-8")
    s = s.replace("Work.", "Checked.")
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! Hiemenz stagnation-point flow, `{key}`: {doc}. Promoted from `Work/Hiemenz/{key}.lean`. -/", s, count=1, flags=re.S)
    assert k == 1, key
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    assert "Work." not in s and "sorry" not in s and "native_decide" not in s, key
    lines = s.splitlines()
    keep = [l for l in lines if l.startswith("import ") and l != "import Mathlib"]
    assert all(not l.startswith("import Mathlib") for l in keep), key
    if imports is None:
        assert "import Mathlib" not in lines, key
        new = keep
    else:
        assert "import Mathlib" in lines, key
        mods = imports + [t for t in TACTICS if t not in imports]
        new = [f"import {m}" for m in mods] + keep
    body = "\n".join(l for l in lines if not l.startswith("import "))
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text("\n".join(new) + "\n" + body.lstrip("\n") + "\n", encoding="utf-8")
    print("wrote", dst.relative_to(ROOT), len(new), "imports")


if __name__ == "__main__":
    for k, (imp, doc) in MODS.items():
        promote(k, imp, doc)
