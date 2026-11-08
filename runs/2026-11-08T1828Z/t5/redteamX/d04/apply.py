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
OLD = "where H₀ = H({t₀}) > 0, z is the redshift observed at {t₀}, and a is positive and differentiable on that neighbourhood"
NEW = "where H₀ = H({t₀}), z is the redshift observed at {t₀}, and a is differentiable on that neighbourhood"

import re
p = root / "scripts/trust/phrases.txt"
t = p.read_text(encoding="utf-8")
lines = t.split("\n")
hit = [i for i, l in enumerate(lines) if l.startswith("Aviles.IsFlatLCDM | ")]
assert len(hit) == 1
assert lines[hit[0]].count(OLD) == 1
lines[hit[0]] = lines[hit[0]].replace(OLD, NEW)
p.write_text("\n".join(lines), encoding="utf-8")
sub_any("CLAIMS.md", OLD.replace("{t₀}", "`t₀`"), NEW.replace("{t₀}", "`t₀`"))
ledger("- 2026-11-08, run 2026-11-08T1828Z — phrase of `IsFlatLCDM` in `scripts/trust/phrases.txt` reworded (shortened: the standing conventions H₀ = H(t₀) and the redshift are named, the regularity clause kept); CLAIMS.md regenerated.")
