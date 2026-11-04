#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def sub(rel, old, new):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, "old text occurs %d times" % t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

sub("Checked/Fidelity/CriticalSpec.lean", '/-- Pin: any predicate meeting `CriticalSpec` agrees with `IsCriticalIsotherm` on every isotherm\nthat is `C²` near the volume considered (from the determining law alone). -/', '/-- Pin: any predicate meeting `CriticalSpec` agrees with `IsCriticalIsotherm` on every isotherm `p`\nand every volume `v`, with no regularity or domain assumption (smooth, kinked or discontinuous\nisotherms alike), from the determining law alone. -/')
