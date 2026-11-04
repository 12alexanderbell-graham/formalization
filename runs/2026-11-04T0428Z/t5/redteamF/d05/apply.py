import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

sub("FINDINGS.md",
    "(flat: (11 − 5q₀ + 3q₀² − j₀)/6).",
    "(flat: (11 − 5q₀ + 3q₀² − j₀)/6; in flat ΛCDM with Ω_m = 3/10, q₀ = −11/20, j₀ = 1 it is `2.76`, and the printed formula gives its negative).")
