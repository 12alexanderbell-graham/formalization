#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
def rep(t, old, new, n=1):
    assert t.count(old) == n, (t.count(old), old[:70])
    return t.replace(old, new)
t = rep(t, "(`F12_separation`, eight decimals), more than one unit of the printed last digit", "(`F12_separation`, eight decimals), more than three units of the printed last digit")

p.write_text(t, encoding="utf-8")
