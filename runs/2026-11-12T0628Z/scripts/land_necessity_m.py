#!/usr/bin/env python3
"""Land run 2026-11-12T0628Z's necessity witnesses (runs/2026-11-12T0628Z/lean/NecessityM.lean) in
Checked/Trust/, import the module in Checked.lean, and shrink scripts/trust/necessity_open_baseline.txt
by the classified hypotheses."""
import pathlib, re
ROOT = pathlib.Path(__file__).resolve().parents[3]
src = (ROOT / "runs/2026-11-12T0628Z/lean/NecessityM.lean").read_text(encoding="utf-8")
(ROOT / "Checked/Trust/NecessityM.lean").write_text(src, encoding="utf-8")
c = (ROOT / "Checked.lean").read_text(encoding="utf-8")
if "import Checked.Trust.NecessityM\n" not in c:
    assert "import Checked.Trust.NecessityL\n" in c
    c = c.replace("import Checked.Trust.NecessityL\n", "import Checked.Trust.NecessityL\nimport Checked.Trust.NecessityM\n", 1)
    (ROOT / "Checked.lean").write_text(c, encoding="utf-8")
CLOSE = {"Math.BonnorEbert.bonnor_ebert_critical": {1, 2, 3, 4, 5},
         "Math.Gelfand.gelfand_ball_critical": {5},
         "Math.ThomasFermi.tf_initial_slope": {1},
         "Math.GelfandPDE.gelfand_pde_radial_bound": {2, 3}}
b = ROOT / "scripts/trust/necessity_open_baseline.txt"
out = []
for line in b.read_text(encoding="utf-8").splitlines():
    m = re.match(r"^(\S+) \| (.*)$", line)
    if m and m.group(1) in CLOSE:
        idx = [int(x) for x in m.group(2).split(", ")]
        assert CLOSE[m.group(1)] <= set(idx), (line, CLOSE[m.group(1)])
        rest = [i for i in idx if i not in CLOSE[m.group(1)]]
        print("baseline:", line, "->", rest)
        if rest:
            out.append(f"{m.group(1)} | {', '.join(map(str, rest))}")
        continue
    out.append(line)
b.write_text("\n".join(out) + "\n", encoding="utf-8")
