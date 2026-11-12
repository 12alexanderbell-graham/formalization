#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
def rep(t, old, new, n=1):
    assert t.count(old) == n, (t.count(old), old[:70])
    return t.replace(old, new)
t = rep(t, "0.005226[src>fs_neg_wall_shear_window] (Salama 2004)", "0.005218[src] (Salama 2004)")

p.write_text(t, encoding="utf-8")
