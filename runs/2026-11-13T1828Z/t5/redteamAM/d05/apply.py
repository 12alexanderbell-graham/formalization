#!/usr/bin/env python3
"""d05: F3's printed value has no reader file (legacy reading), so the generated Printed line says the source is not
described; the heading (author title) is then the only statement of which paper version prints it, and it is changed."""
import subprocess, sys
from pathlib import Path

root = Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
old = "arXiv:0802.1583v2, App. A, Eq. (A2): lookback-distance"
new = "arXiv:0802.1583v1, App. A, Eq. (A2): lookback-distance"
assert t.count(old) == 1
p.write_text(t.replace(old, new), encoding="utf-8")

led = root / "LEDGER.md"
s = led.read_text(encoding="utf-8")
if not s.endswith("\n"):
    s += "\n"
s += "- 2026-11-13, run 2026-11-13T1828Z — `FINDINGS.md` `F3`: heading's version label revised.\n"
led.write_text(s, encoding="utf-8")

subprocess.run([sys.executable, "validation/make_packet.py"], cwd=root, check=True, stdout=subprocess.DEVNULL)
