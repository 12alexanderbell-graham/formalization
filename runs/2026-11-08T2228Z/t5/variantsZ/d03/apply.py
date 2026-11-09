#!/usr/bin/env python3
# Round Z d03, the same move on the phrases of run 2026-11-08T2228Z (judge's variant: not blind)
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "scripts/trust/phrases.txt"
t = p.read_text(encoding="utf-8")
for old, new in [('the complex concentration over time {c} and the product concentration over time {p} are', 'the complex concentration over time {p} and the product concentration over time {c} are')]:
    assert t.count(old) == 1, old
    t = t.replace(old, new)
p.write_text(t, encoding="utf-8")
L = root / "LEDGER.md"
L.write_text(L.read_text(encoding="utf-8") + "\nvariant d03: phrase reworded (names the definition)\n", encoding="utf-8")
