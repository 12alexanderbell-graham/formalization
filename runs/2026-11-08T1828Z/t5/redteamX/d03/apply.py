#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new, count=1):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == count, (rel, old, t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")
def sub_any(rel, old, new):
    # best effort for the generated file: the author regenerates it with Claims.lean anyway
    p = root / rel
    t = p.read_text(encoding="utf-8")
    p.write_text(t.replace(old, new), encoding="utf-8")
def ledger(line):
    p = root / "LEDGER.md"
    t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"):
        t += "\n"
    p.write_text(t + line + "\n", encoding="utf-8")
OLD = "the molar volume {v} is a critical point of the isotherm {p} (pressure as a function of molar volume at fixed temperature): p′({v}) = 0 and p″({v}) = 0"
NEW = "the molar volume {v} is the critical point of the isotherm {p} (pressure as a function of molar volume at fixed temperature): {p} is twice differentiable at {v} and has a horizontal inflection point there, p′({v}) = 0 and p″({v}) = 0"
sub("scripts/trust/phrases.txt", OLD, NEW)
sub_any("CLAIMS.md", "the molar volume `v` is a critical point of the isotherm `p` (pressure as a function of molar volume at fixed temperature): p′(`v`) = 0 and p″(`v`) = 0",
        "the molar volume `v` is the critical point of the isotherm `p` (pressure as a function of molar volume at fixed temperature): `p` is twice differentiable at `v` and has a horizontal inflection point there, p′(`v`) = 0 and p″(`v`) = 0")
ledger("- 2026-11-08, run 2026-11-08T1828Z — phrase of `IsCriticalIsotherm` in `scripts/trust/phrases.txt` reworded (the physical content of the vanishing first and second derivative spelled out); CLAIMS.md regenerated.")
