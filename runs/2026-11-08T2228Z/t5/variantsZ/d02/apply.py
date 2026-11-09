#!/usr/bin/env python3
# Round Z d02, the same move on the phrases of run 2026-11-08T2228Z (judge's variant: not blind)
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "scripts/trust/phrases.txt"
t = p.read_text(encoding="utf-8")
for old, new in [('the luminosity distance in FLRW with curvature, at the observation time {t₀}, of a source at the emission time {t},', 'the luminosity distance in FLRW with curvature, at the observation time {t}, of a source at the emission time {t₀},')]:
    assert t.count(old) == 1, old
    t = t.replace(old, new)
p.write_text(t, encoding="utf-8")
L = root / "LEDGER.md"
L.write_text(L.read_text(encoding="utf-8") + "\nvariant d02: phrase reworded (names the definition)\n", encoding="utf-8")
