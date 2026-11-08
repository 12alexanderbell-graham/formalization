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
sub(PH, "(units in which the speed of light is one; it is minus Ω_k)", "(units in which the speed of light is one; it is the curvature density parameter Ω_k)")
sub(PH, "(units in which the speed of light is one; Ω_k is one minus Ω₀)", "(units in which the speed of light is one)")
ledger("Run 2026-11-08T1828Z+1: phrases of `curvK` and `omega0` reworded to name Ω_k directly instead of by a relation between the two; bodies, pins and headlines unchanged.")
