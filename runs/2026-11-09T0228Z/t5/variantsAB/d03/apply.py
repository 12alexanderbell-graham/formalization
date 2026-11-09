#!/usr/bin/env python3
"""Judge's variant of adversary AB d01: the same move applied to this run's phrases (run 2026-11-09T0228Z)."""
import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new), encoding="utf-8")
PH = "scripts/trust/phrases.txt"
REG = "scripts/trust/phrase_roles.txt"
sub(PH, "over the scale factor divided by the {n}-th power of the Hubble rate;", "over the scale factor;")
