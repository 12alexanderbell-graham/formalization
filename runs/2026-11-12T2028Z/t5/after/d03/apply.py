#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
def rep(t, old, new, n=1):
    assert t.count(old) == n, (t.count(old), old[:70])
    return t.replace(old, new)
t = rep(t, "`fs_neg_wall_shear_two_decay` (two solutions of that class with different wall shear: non-uniqueness just above separation)",
        "`fs_neg_wall_shear_two_decay` (the decay-class solution with f' bounded by 1 is unique for its wall shear: the printed value and the certified one cannot both belong to it)")

p.write_text(t, encoding="utf-8")
