#!/usr/bin/env python3
"""Builds SpecAgreementIJK.lean = imports + readers I, J and K files with code unchanged (their import
lines dropped, the imports hoisted) + the closure theorems of theorems.lean. Run from the repository root:
python3 runs/2026-11-27T1028Z/agreement/mk_agreement.py   (run 2026-11-27T1028Z; LOCK held by another run,
so the closure lives here; a later run copies the readers to Checked/Trust and this theorem part beside them)."""
from pathlib import Path
R = Path(__file__).resolve().parents[1]
imports = ["import Checked.Cosmography.FRCosmo"]
bodies = []
for L in "IJK":
    lines = (R / f"spec{L}" / f"SecondReadingSpec{L}.lean").read_text().splitlines()
    imports += [l for l in lines if l.startswith("import ")]
    bodies.append("\n".join(l for l in lines if not l.startswith("import ")))
seen, imp = set(), []
for l in imports:
    if l not in seen:
        seen.add(l); imp.append(l)
out = "\n".join(imp) + "\n" + "\n\n".join(bodies) + "\n\n" + (R / "agreement" / "theorems.lean").read_text()
(R / "agreement" / "SpecAgreementIJK.lean").write_text(out)
print("wrote", R / "agreement" / "SpecAgreementIJK.lean")
