#!/usr/bin/env python3
"""Run 2026-11-20T1228Z: promote the Work proof that hypothesis 1 of gelfand_pde_radial_exists is redundant.
Work/Math/GelfandNeg{Left,Right,Profile,Exists}.lean -> Checked/Math/GNeg{Left,Right,Profile,Exists}.lean (namespaces
renamed, #print axioms lines dropped, the redundancy theorem moved to Checked/Trust/NecessityBE.lean)."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
names = {"GelfandNegLeft": "GNegLeft", "GelfandNegRight": "GNegRight", "GelfandNegProfile": "GNegProfile",
         "GelfandNegExists": "GNegExists"}
def conv(s):
    for a, b in names.items():
        s = s.replace(f"Work.Math.{a}", f"Checked.Math.{b}")
    return s
for a, b in names.items():
    s = (R / f"Work/Math/{a}.lean").read_text()
    s = conv(s)
    s = "\n".join(l for l in s.split("\n") if not l.startswith("#print axioms"))
    if a == "GelfandNegExists":
        i = s.index("theorem gelfand_pde_radial_exists_r1")
        j = s.index("end Checked.Math.GNegExists")
        r1 = s[i:j].rstrip() + "\n"
        s = s[:i] + s[j:]
        s = s.replace("import Checked.Trust.NonVacuity\n", "")
        r1 = r1.replace("exact exists_nonpos", "exact Checked.Math.GNegExists.exists_nonpos")
        (R / "Checked/Trust/NecessityBE.lean").write_text(
            "import Checked.Trust.NonVacuity\nimport Checked.Math.GNegExists\n\n"
            "/-! Hypothesis necessity for `Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists` (run 2026-11-20T1228Z):\n"
            "the positivity of the parameter is redundant, because a radial classical solution exists for every\n"
            "non-positive parameter too (`Checked.Math.GNegExists.exists_nonpos`: the zero function at zero; below zero a\n"
            "clamped radial profile of the equation with the opposite sign, rescaled so that it vanishes on the sphere).\n"
            "Module `NecessityBE`. -/\n\nnamespace Checked.Trust.NecessityBE\n\n" + r1 + "\nend Checked.Trust.NecessityBE\n")
    s = re.sub(r"\n{3,}", "\n\n", s)
    (R / f"Checked/Math/{b}.lean").write_text(s)
c = (R / "Checked.lean").read_text()
for b in ["GNegLeft", "GNegRight", "GNegProfile", "GNegExists"]:
    line = f"import Checked.Math.{b}\n"
    if line not in c:
        c = c.replace("import Checked.Math.GLam3Chain\n", "import Checked.Math.GLam3Chain\n" + line, 1)
if "import Checked.Trust.NecessityBE\n" not in c:
    c = c.replace("import Checked.Trust.NecessityBD\n", "import Checked.Trust.NecessityBD\nimport Checked.Trust.NecessityBE\n", 1)
(R / "Checked.lean").write_text(c)
print("ok")
