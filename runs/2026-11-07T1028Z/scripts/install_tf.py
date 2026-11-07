#!/usr/bin/env python3
"""Install the kernel-evaluated Thomas–Fermi chain (run 2026-11-07T1028Z) into Checked.

Copies runs/2026-11-07T1028Z/lean/{TFCellQ,TFQData,TFChain}.lean to Checked/Math/ (TFChain keeps its
statements, namespace and module doc; it no longer imports the certificate modules) and moves the nine
`ring`-certificate modules Checked/Math/TFCerts{Sup,Sub}*.lean to _archive/Checked/Math/ (48.3: never
delete). Needs Checked/Sim/QPoly.lean (the Townes promotion). Afterwards: relock (the nine module docs
leave frozen.txt, TFCellQ/TFQData module docs enter it) and a LEDGER line naming them.

usage: install_tf.py <repo root>
"""
import shutil
import sys
from pathlib import Path

root = Path(sys.argv[1])
src = root / "runs/2026-11-07T1028Z/lean"
assert (root / "Checked/Sim/QPoly.lean").exists(), "Checked/Sim/QPoly.lean missing: merge the Townes promotion first"
for name in ["TFCellQ.lean", "TFQData.lean", "TFChain.lean"]:
    shutil.copy(src / name, root / "Checked/Math" / name)
arch = root / "_archive/Checked/Math"
arch.mkdir(parents=True, exist_ok=True)
moved = []
for f in sorted((root / "Checked/Math").glob("TFCerts*.lean")):
    assert not (arch / f.name).exists(), f
    shutil.move(str(f), str(arch / f.name))
    moved.append(f.name)
assert len(moved) == 9, moved
checked = (root / "Checked.lean").read_text()
for m in moved:
    line = f"import Checked.Math.{m[:-5]}\n"
    checked = checked.replace(line, "")
for m in ["TFCellQ", "TFQData"]:
    line = f"import Checked.Math.{m}\n"
    if line not in checked:
        checked = checked.replace("import Checked.Math.TFChain\n", line + "import Checked.Math.TFChain\n")
(root / "Checked.lean").write_text(checked)
print("installed; archived:", " ".join(moved))
