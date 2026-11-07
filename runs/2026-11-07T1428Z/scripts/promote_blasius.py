#!/usr/bin/env python3
"""Promote the Blasius pair (blasius_wall_shear, blasius_exists) and its supporting modules from Work to Checked
(run 2026-11-07T1428Z; pattern of runs/2026-11-07T0828Z/scripts/promote_townes.py).

Mechanical copy: `Work.` -> `Checked.` in every name, module docs replaced by number-free text (check_prose
rule 7), `#print axioms` lines dropped. Statements and proofs otherwise byte-identical to Work. Imports:
`import Mathlib` is replaced by the specific modules `#min_imports` reports (second pass,
`--imports <key> <file with the list>`), plus the five tactic modules.
"""
import re, sys, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
DOCS = {
    "BTail": "the Blasius system f' = p, p' = q, q' = −f q/2 on the half-line: the wall value of q is positive for every solution with the stated wall and edge conditions, the scaling symmetry, and the bound on the edge value of p from the state at a finite point by a non-increasing functional",
    "BCell": "one validated Grönwall step of the three-dimensional Blasius system on a slab where its field is Lipschitz",
    "BCellQ": "validated cells and chains of cells of the Blasius system, each from one Boolean check over the rationals decided by kernel evaluation",
    "BQData": "the cells of the Blasius initial-value problem with unit wall value of q, checked by kernel evaluation, and the resulting enclosure of the state at the end of the chain",
    "Blasius": "the wall shear of the Blasius boundary layer, as printed in the statement of `blasius_wall_shear`, from the scaling symmetry, the validated chain and the tail bound",
    "BExBase": "the Blasius field with its components clamped, globally Lipschitz on every bounded time interval",
    "BExFlow": "a global solution of the clamped Blasius system from the wall state with unit value of q",
    "BExBounds": "along the clamped flow every clamp is inactive, so its components solve the Blasius system, and p increases to a positive limit",
    "BlasiusExists": "existence of a solution of the Blasius boundary-layer problem, as printed in the statement of `blasius_exists`",
}
def promote(key):
    src = ROOT / "Work" / "Blasius" / f"{key}.lean"
    dst = ROOT / "Checked" / "Blasius" / f"{key}.lean"
    s = src.read_text(encoding="utf-8")
    s = s.replace("Work.", "Checked.")
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! Blasius boundary layer, `{key}`: {DOCS[key]}. Promoted from `Work/Blasius/{key}.lean`. -/", s, count=1, flags=re.S)
    assert k == 1, key
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    assert "Work." not in s and "sorry" not in s, key
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(s, encoding="utf-8")
    print("wrote", dst.relative_to(ROOT))

def set_imports(key, listfile):
    dst = ROOT / "Checked" / "Blasius" / f"{key}.lean"
    s = dst.read_text(encoding="utf-8")
    mods = [l.strip() for l in open(listfile) if l.strip()]
    keep = [l for l in s.splitlines() if l.startswith("import ") and not l.startswith("import Mathlib")]
    tactics = [f"Mathlib.Tactic.{t}" for t in ("NormNum", "Linarith", "Ring", "FieldSimp", "Positivity")]
    mods = mods + [t for t in tactics if t not in mods]
    new = [f"import {m}" for m in mods if f"import {m}" not in keep] + keep
    body = "\n".join(l for l in s.splitlines() if not l.startswith("import "))
    dst.write_text("\n".join(new) + "\n" + body.lstrip("\n") + ("\n" if not body.endswith("\n") else ""), encoding="utf-8")
    assert "import Mathlib\n" not in dst.read_text()
    print("imports", key, len(new))

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--imports":
        set_imports(sys.argv[2], sys.argv[3])
    else:
        for k in DOCS:
            promote(k)
