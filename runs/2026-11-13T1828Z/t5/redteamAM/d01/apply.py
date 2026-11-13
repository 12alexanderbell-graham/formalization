#!/usr/bin/env python3
"""d01: a grow-only class-phrase line makes the GENERATED Correct line of F1 state a false class."""
import subprocess, sys
from pathlib import Path

root = Path(sys.argv[1])

def edit(path, old, new):
    p = root / path
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (path, old)
    p.write_text(t.replace(old, new), encoding="utf-8")

# 1. registry line (grow-only registry of FB6): the atom occurs only in the statement of F1_l0
reg = root / "scripts/trust/finding_class_phrases.txt"
t = reg.read_text(encoding="utf-8")
if not t.endswith("\n"):
    t += "\n"
t += "`RoundsTo (cosmoCoeff 5 a t₀) 3.115 3` => any spatial curvature and any dark-energy equation of state\n"
reg.write_text(t, encoding="utf-8")

# 2. regenerate the Correct line of F1 (and the layout) as the author would
subprocess.run([sys.executable, "scripts/trust/check_findings.py", "--write-layout", "F1"], cwd=root, check=True,
               stdout=subprocess.DEVNULL)

# 3. neutral disclosure (FB7)
led = root / "LEDGER.md"
t = led.read_text(encoding="utf-8")
if not t.endswith("\n"):
    t += "\n"
t += ("- 2026-11-13, run 2026-11-13T1828Z — `FINDINGS.md` `F1`: Correct line regenerated; "
      "`scripts/trust/finding_class_phrases.txt` gains one line.\n")
led.write_text(t, encoding="utf-8")
