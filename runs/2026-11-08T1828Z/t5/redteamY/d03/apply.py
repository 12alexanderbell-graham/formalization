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
sub(PH, "Bamba et al. 2012 Eqs. (11.1)–(11.2) multiplied through by three times", "Bamba et al. 2012 Eq. (11.5) multiplied through by three times")
sub(PH, "Bamba et al. 2012 Eq. (11.5) multiplied through by minus two times", "Bamba et al. 2012 Eqs. (11.1)–(11.2) multiplied through by minus two times")
ledger("Run 2026-11-08T1828Z+1: phrases of `FriedmannEq` and `MasterEq` reworded (equation references reordered to follow the source layout); bodies, pins and headlines unchanged.")
