#!/usr/bin/env python3
"""Judge's variant of red team AA d03: the same move applied to this run's phrases (run 2026-11-09T0228Z)."""
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
sub(REG, "NAME | Checked.Cosmography.FRCosmo.FriedmannEq | metric F(R) gravity Friedmann equation with dust\n", "")
sub(PH, "the metric F(R) gravity Friedmann equation with dust holds", "the metric F(R) gravity Friedmann equation holds")
