#!/usr/bin/env python3
"""Install the kernel-evaluated certificate chains of run 2026-11-07T1028Z into Checked.

Thomas–Fermi: TFCellQ, TFQData, TFChain (statements, namespace and module doc of TFChain unchanged);
the nine `ring`-certificate modules TFCerts{Sup1-4,Sub1-5} move to _archive/Checked/Math/.
Lane–Emden: LECellQ, LEQData, LELast (step89 and lastFacts copied verbatim from LECerts3), LEChain
(statement and module doc unchanged); LECerts1-3 move to _archive/Checked/Math/ (LECerts, the start,
stays). 48.3: never delete. Needs Checked/Sim/QPoly.lean (the Townes promotion). Afterwards: relock
(module docs of the archived modules leave frozen.txt, the new ones enter it) and a LEDGER line naming them.

usage: install_tf.py <repo root>
"""
import shutil
import sys
from pathlib import Path

root = Path(sys.argv[1])
src = root / "runs/2026-11-07T1028Z/lean"
assert (root / "Checked/Sim/QPoly.lean").exists(), "Checked/Sim/QPoly.lean missing: merge the Townes promotion first"
NEW = {"TFChain": ["TFCellQ", "TFQData"], "LEChain": ["LECellQ", "LEQData", "LELast"]}
OLD = [f"TFCertsSup{i}" for i in range(1, 5)] + [f"TFCertsSub{i}" for i in range(1, 6)] + [f"LECerts{i}" for i in (1, 2, 3)]
for chain, mods in NEW.items():
    for m in mods + [chain]:
        shutil.copy(src / f"{m}.lean", root / "Checked/Math" / f"{m}.lean")
arch = root / "_archive/Checked/Math"
arch.mkdir(parents=True, exist_ok=True)
for m in OLD:
    f = root / "Checked/Math" / f"{m}.lean"
    assert f.exists() and not (arch / f.name).exists(), f
    shutil.move(str(f), str(arch / f.name))
checked = (root / "Checked.lean").read_text()
for m in OLD:
    line = f"import Checked.Math.{m}\n"
    assert line in checked, line
    checked = checked.replace(line, "")
for chain, mods in NEW.items():
    anchor = f"import Checked.Math.{chain}\n"
    assert anchor in checked
    add = "".join(f"import Checked.Math.{m}\n" for m in mods if f"import Checked.Math.{m}\n" not in checked)
    checked = checked.replace(anchor, add + anchor)
(root / "Checked.lean").write_text(checked)
print("installed; archived:", " ".join(OLD))
