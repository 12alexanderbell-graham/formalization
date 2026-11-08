#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(path, old, new):
    p = root / path
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (path, old)
    p.write_text(t.replace(old, new), encoding="utf-8")
PH = "scripts/trust/phrases.txt"
def ledger(line):
    p = root / "LEDGER.md"
    t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"): t += "\n"
    p.write_text(t + line + "\n", encoding="utf-8")
sub(PH, "the deceleration parameter of the scale factor {a} at time {t}\n", "the deceleration parameter of the scale factor {a} at time {t} (not defined where the first derivative of {a} vanishes, and no claim is made there)\n")
ledger("Run 2026-11-08T1828Z+1: phrase of `decel` reworded (states where the quantity is meaningful); body, pin and headlines unchanged.")
