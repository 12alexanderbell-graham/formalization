#!/usr/bin/env python3
"""Judge's variant of red team AA d04: the same move applied to this run's phrases (run 2026-11-09T0228Z)."""
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
sub(REG, "SIGN | Checked.Cosmography.BambaZ.curvK | has sign of curvature constant, minus the curvature density parameter\n", "")
sub(PH, "(has sign of curvature constant, minus the curvature density parameter; total", "(has sign of curvature constant and is the curvature density parameter; total")
