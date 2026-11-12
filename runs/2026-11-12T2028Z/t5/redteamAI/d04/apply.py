#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
def rep(t, old, new, n=1):
    assert t.count(old) == n, (t.count(old), old[:70])
    return t.replace(old, new)
import re
def block(name):
    m = re.search(r"<!-- certified: " + name + r" -->\n.*?<!-- /certified -->\n", t, re.S)
    assert m
    return m.group(0)
b13, b14 = block("F13_wall_shear"), block("F14_reversed_wall_shear")
assert t.count(b13) == 1 and t.count(b14) == 1
t = t.replace(b13, "@@B13@@").replace(b14, "@@B14@@")
t = t.replace("@@B13@@", b14).replace("@@B14@@", b13)

p.write_text(t, encoding="utf-8")
