#!/usr/bin/env python3
"""Promote the Townes trio (townes_under, townes_over, townes_exists) and its supporting modules from Work to
Checked (run 2026-11-07T0828Z).

Mechanical copy: `Work.` -> `Checked.` in every name (the Checked versions of `Work.Sim.ODETools` and
`Work.Math.LECell` already exist with the same declarations), module docs replaced by number-free text
(check_prose rule 7), `#print axioms` lines dropped. Statements and proofs are otherwise byte-identical to
Work. Imports: `import Mathlib` is kept here and replaced by the specific modules `#min_imports` reports
(second pass, `--imports <module> <file with the list>`).
"""
import re, sys, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
DOCS = {
    "Sim/QPoly": "rational polynomial arithmetic on coefficient lists (sum, product, derivative, evaluation) with the lemmas that evaluating a computed list at a real point gives the corresponding real expression, so that defect bounds of validated cells are decided by kernel evaluation",
    "Townes/TCell": "one validated Grönwall step of the Townes radial system on a slab where its field is Lipschitz, with the defect of the second component in multiplied-out form",
    "Townes/TStart": "the singular start of the Townes radial equation: every solution stays close to a truncated power series near the centre, by comparison and continuous induction",
    "Townes/TCellQ": "validated cells, chains of cells and the singular start of the Townes radial equation, each from one Boolean check over the rationals decided by kernel evaluation",
    "Townes/TQDataA": "the cells and the singular start of the undershoot run of the Townes radial equation, checked by kernel evaluation, and the resulting enclosure",
    "Townes/TQDataB": "the cells and the singular start of the overshoot run of the Townes radial equation, checked by kernel evaluation, and the resulting enclosure",
    "Townes/TownesShooting": "the two shooting events of the Townes radial equation, undershoot and overshoot, as printed in the statements of `townes_under` and `townes_over`",
    "Townes/TExLeft": "a family of solutions of the Townes radial equation regular at the centre, as fixed points of a contraction depending on the central value",
    "Townes/TExFlow": "the clamped continuation of the Townes radial system away from the centre, Lipschitz in the initial state, with an energy that keeps the clamps inactive",
    "Townes/TExLimit": "a solution of the Townes radial equation with neither shooting event is positive, decreasing and tends to zero",
    "Townes/TExAssemble": "the shooting argument: open exclusive events and the supremum of the undershoot central values",
    "Townes/TownesExists": "existence of a ground state of the Townes radial equation with central value in the bracket printed in the statement of `townes_exists`",
    "Townes/TownesSolutions": "solutions of the initial-value problem of the Townes radial equation at the singular point exist for central values in an interval (non-vacuity of the shooting statements)",
}
def promote(key):
    src = ROOT / "Work" / f"{key}.lean"
    dst = ROOT / "Checked" / f"{key}.lean"
    s = src.read_text(encoding="utf-8")
    s = s.replace("Work.", "Checked.")
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! {'Validated simulation' if key.startswith('Sim/') else 'Townes ground state'}, `{key.split('/')[-1]}`: {DOCS[key]}. Promoted from `Work/{key}.lean`. -/", s, count=1, flags=re.S)
    assert k == 1, key
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    assert "Work." not in s and "sorry" not in s, key
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(s, encoding="utf-8")
    print("wrote", dst.relative_to(ROOT))

def set_imports(key, listfile):
    dst = ROOT / "Checked" / f"{key}.lean"
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
