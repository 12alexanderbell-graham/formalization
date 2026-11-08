#!/usr/bin/env python3
"""Promote the bounded-class theorems of run 2026-11-08T1228Z from Work to Checked (pattern of
runs/2026-11-08T1028Z/scripts/promote_mw.py): `Work.` -> `Checked.` in every name, module docs
replaced by number-free text, `import Mathlib` replaced by the modules `#min_imports` reports plus
tactic modules. Statements and proofs otherwise byte-identical to Work."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
MATH = ["Mathlib.Analysis.ODE.ExistUnique"]
TACTICS = [f"Mathlib.Tactic.{t}" for t in ("NormNum", "Linarith", "Ring", "FieldSimp", "Positivity", "FunProp")]
MODS = {
    "FalknerSkan/BoundedTools": "Stagnation-point equations written as a first-order system with a real coefficient of the product term: a velocity profile strictly between minus one and one that tends to one has positive second derivative on the closed half-line; a profile starting at zero and bounded by one in absolute value stays strictly inside; two solutions with the same start values agree on the closed half-line",
    "FalknerSkan/Bounded": "Hiemenz and Homann stagnation-point flows: every solution of the boundary-value problem whose velocity profile is bounded by one in absolute value on the closed half-line has its wall shear inside the certified window, any two such solutions are equal on the closed half-line, and a solution with velocity profile in the half-open unit interval exists",
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
