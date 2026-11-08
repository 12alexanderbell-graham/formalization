#!/usr/bin/env python3
"""Promote the monotone-solution theorems of run 2026-11-08T1028Z from Work to Checked
(pattern of runs/2026-11-08T0828Z/scripts/promote_fs.py): `Work.` -> `Checked.` in every name,
module docs replaced by number-free text (check_prose rule 7), `import Mathlib` replaced by the
modules `#min_imports` reports for the three Crocco modules plus the five tactic modules.
Statements and proofs otherwise byte-identical to Work."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
MATH = ["Mathlib.Algebra.Order.Star.Real", "Mathlib.Analysis.Calculus.Deriv.Inverse",
        "Mathlib.Analysis.Calculus.Deriv.MeanValue", "Mathlib.Analysis.InnerProductSpace.Basic",
        "Mathlib.Analysis.LocallyConvex.AbsConvexOpen", "Mathlib.Topology.Algebra.Module.ModuleTopology"]
TACTICS = [f"Mathlib.Tactic.{t}" for t in ("NormNum", "Linarith", "Ring", "FieldSimp", "Positivity")]
MODS = {
    "FalknerSkan/CroccoCompare": "Crocco variables, a cooperative comparison: two curves of the Crocco system of the stagnation-point equations (non-negative coefficient of the product term) with equal F at the start and ordered z there keep the difference of their z at least its starting value on a common range below one",
    "FalknerSkan/CroccoMap": "Crocco variables, the change of variables: on an interval where the second derivative is positive, the first derivative is inverted and the second derivative and the function, as functions of the first derivative, satisfy the Crocco system",
    "FalknerSkan/CroccoWindow": "Crocco variables, comparison of a boundary-value solution with positive second derivative against an overshooting or an undershooting solution of the initial-value problem, generic in the non-negative coefficient of the product term",
    "FalknerSkan/MonotoneWindow": "Hiemenz and Homann stagnation-point flows: every solution of the boundary-value problem with positive second derivative on the closed half-line has its wall shear inside the window printed in the statements of `hiemenz_monotone_window` and `homann_monotone_window`, the ends of which are the certified shooting values",
    "Hiemenz/HExMono": "Hiemenz stagnation-point flow: the shooting construction of the existence theorem with the positivity of the second derivative on the closed half-line, which the construction proves, added to its conclusion",
    "Homann/HmExMono": "Homann stagnation-point flow: the shooting construction of the existence theorem with the positivity of the second derivative on the closed half-line, which the construction proves, added to its conclusion",
    "FalknerSkan/MonotoneExists": "Hiemenz and Homann stagnation-point flows: there is a solution of the boundary-value problem with positive second derivative on the closed half-line and wall shear in the certified window, and solutions with positive second derivative share one wall shear",
}

def promote(key, doc):
    src = ROOT / "Work" / f"{key}.lean"
    dst = ROOT / "Checked" / f"{key}.lean"
    s = src.read_text(encoding="utf-8")
    s = s.replace("Work.", "Checked.")
    name = key.split("/")[1]
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! {doc}. Module `{name}`, promoted from `Work/{key}.lean`. -/", s, count=1, flags=re.S)
    assert k == 1, key
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    assert "Work." not in s and "sorry" not in s and "native_decide" not in s, key
    lines = s.splitlines()
    keep = [l for l in lines if l.startswith("import ") and l != "import Mathlib"]
    new = keep
    if "import Mathlib" in lines:
        new = [f"import {m}" for m in MATH + TACTICS] + keep
    body = "\n".join(l for l in lines if not l.startswith("import "))
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text("\n".join(new) + "\n" + body.lstrip("\n") + "\n", encoding="utf-8")
    print("wrote", dst.relative_to(ROOT), len(new), "imports")

if __name__ == "__main__":
    for k, d in MODS.items():
        promote(k, d)
