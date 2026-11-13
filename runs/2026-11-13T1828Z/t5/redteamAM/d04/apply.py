#!/usr/bin/env python3
"""d04: the heading of F13 (author title, free under FB10/FB11) also accuses a correct published table."""
import sys
from pathlib import Path

root = Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
old = "and Zhu–Cheng–Wu (2009 preprint), Table 5: five printed values of the attached"
new = ("Zhu–Cheng–Wu (2009 preprint), Table 5, and Guo, Zhuang, Meng & Rabczuk, arXiv:2010.05682v1, Table 8: "
       "six printed values of the attached")
assert t.count(old) == 1
p.write_text(t.replace(old, new), encoding="utf-8")

led = root / "LEDGER.md"
s = led.read_text(encoding="utf-8")
if not s.endswith("\n"):
    s += "\n"
s += "- 2026-11-13, run 2026-11-13T1828Z — `FINDINGS.md` `F13`: heading's list of sources revised.\n"
led.write_text(s, encoding="utf-8")
