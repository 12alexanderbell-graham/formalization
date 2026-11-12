#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
def rep(t, old, new, n=1):
    assert t.count(old) == n, (t.count(old), old[:70])
    return t.replace(old, new)
t = rep(t, "with f'' > 0 beyond the wall and faster-than-every-exponential approach to the edge velocity lies below the printed value",
        "with f'' > 0 beyond the wall lies below the printed value")
t = rep(t, "for parameters between the separation value and 0 a zero-wall-shear solution with an algebraic tail exists, so the caption is false only in the classical class (exponential approach), the class in which the paper calls the solution unique.",
        "every zero-wall-shear solution with f'' > 0, whatever its approach to the edge velocity, has a parameter below the printed value, so the caption is false in general (no restriction to the classical class).")

p.write_text(t, encoding="utf-8")
