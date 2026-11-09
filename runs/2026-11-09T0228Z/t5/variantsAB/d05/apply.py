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
sub(REG, "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | The order 5 coefficient is the lerk parameter usually written l\n", "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | The order 5 coefficient is the lerk parameter usually written l\nCLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | q j s l for the orders 2 3 4 5\n")
sub(PH, "usually written l)", "usually written l; q j s l for the orders 2 3 4 5)")
