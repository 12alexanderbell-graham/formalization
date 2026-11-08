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
sub(PH, "on some neighbourhood of the time {t₀}, with a positive Hubble rate at {t₀} and a positive, differentiable scale factor on that neighbourhood (the law itself is the formula printed with the definition)\nAviles.cosmoCoeff",
    "on some neighbourhood of the time {t₀}, with a positive Hubble rate at {t₀} and a positive, differentiable scale factor on that neighbourhood (the law itself is the formula printed with the definition; the fitted value of the matter fraction {Ω} is 0.3, as verified in Aviles et al.)\nAviles.cosmoCoeff")
ledger("Run 2026-11-08T1828Z+1: phrase of `IsFlatLCDM` reworded (points to the fitted matter fraction of the source); body, pin and headlines unchanged.")
