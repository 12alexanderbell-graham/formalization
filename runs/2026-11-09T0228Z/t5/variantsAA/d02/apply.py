#!/usr/bin/env python3
"""Judge's variant of red team AA d02: the same move applied to this run's phrases (run 2026-11-09T0228Z)."""
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
sub(PH, "B plus C gives A plus C with rate constant {k₂}; two B give B plus C with rate constant {k₃}", "B plus C gives A plus C with rate constant {k₃}; two B give B plus C with rate constant {k₂}")
