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
OLD = "{y₁}′ = −{k₁}·{y₁} + {k₂}·{y₂}·{y₃}, {y₂}′ = {k₁}·{y₁} − {k₂}·{y₂}·{y₃} − {k₃}·{y₂}², {y₃}′ = {k₃}·{y₂}²"
NEW = "{y₁}′ = −{k₁}·{y₁} + {k₃}·{y₂}·{y₃}, {y₂}′ = {k₁}·{y₁} − {k₃}·{y₂}·{y₃} − {k₂}·{y₂}², {y₃}′ = {k₂}·{y₂}²"
sub("scripts/trust/phrases.txt", OLD, NEW)
sub_any("CLAIMS.md", "`y₁`′ = −`k₁`·`y₁` + `k₂`·`y₂`·`y₃`, `y₂`′ = `k₁`·`y₁` − `k₂`·`y₂`·`y₃` − `k₃`·`y₂`², `y₃`′ = `k₃`·`y₂`²",
        "`y₁`′ = −`k₁`·`y₁` + `k₃`·`y₂`·`y₃`, `y₂`′ = `k₁`·`y₁` − `k₃`·`y₂`·`y₃` − `k₂`·`y₂`², `y₃`′ = `k₂`·`y₂`²")
ledger("- 2026-11-08, run 2026-11-08T1828Z — phrase of `IsRobSolution` in `scripts/trust/phrases.txt` reworded (rate constants listed in the order of the network's reactions); CLAIMS.md regenerated.")
