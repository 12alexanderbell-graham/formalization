#!/usr/bin/env python3
"""Promote the Falkner–Skan rows (fs_half_exists, fs_zero_wall_shear) and the scaling module from Work to
Checked (run 2026-11-08T0828Z; pattern of runs/2026-11-08T0428Z/scripts/promote_homann.py).

Mechanical copy: `Work.` -> `Checked.` in every name, module docs replaced by number-free text (check_prose
rule 7), `#print axioms` lines dropped, `import Mathlib` replaced by specific modules (the Blasius headline's
import set plus the five tactic modules). Statements and proofs otherwise byte-identical to Work.
"""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = ["Mathlib.Algebra.Order.Star.Real", "Mathlib.Analysis.LocallyConvex.AbsConvexOpen",
        "Mathlib.Analysis.ODE.ExistUnique", "Mathlib.Analysis.SpecialFunctions.Pow.Real"]
MODS = {
    "FSScale": (BASE, "the similarity scaling of the Falkner–Skan system: for a positive constant c, a solution (f, p, q) of f' = p, p' = q, q' = −a f q − b (1 − p²) within the closed half-line gives the solution s ↦ (c f(s/c), p(s/c), q(s/c)/c) of the same system with a/c² and b/c², with the same limit of p at infinity; and rational bounds on the square root of two"),
    "FalknerSkan": (BASE, "two rows of the Falkner–Skan wall-shear table, obtained from the certified Homann and Blasius theorems by the similarity scaling with c the square root of two: existence of a solution of the half-β problem with wall shear in the window printed in the statement of `fs_half_exists`, and the window printed in the statement of `fs_zero_wall_shear` for the wall shear of every solution of the β-zero problem; uniqueness of the half-β solution is not formalised"),
}
TACTICS = [f"Mathlib.Tactic.{t}" for t in ("NormNum", "Linarith", "Ring", "FieldSimp", "Positivity")]


def promote(key, imports, doc):
    src = ROOT / "Work" / "FalknerSkan" / f"{key}.lean"
    dst = ROOT / "Checked" / "FalknerSkan" / f"{key}.lean"
    s = src.read_text(encoding="utf-8")
    s = s.replace("Work.", "Checked.")
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! Falkner–Skan rows, `{key}`: {doc}. Promoted from `Work/FalknerSkan/{key}.lean`. -/", s, count=1, flags=re.S)
    assert k == 1, key
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    assert "Work." not in s and "sorry" not in s and "native_decide" not in s, key
    lines = s.splitlines()
    keep = [l for l in lines if l.startswith("import ") and l != "import Mathlib"]
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
