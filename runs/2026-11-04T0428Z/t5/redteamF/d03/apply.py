import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

sub("STATE.md",
    "`cubic_misses_z3` (> 0.09 mag), `cubic_misses_z7` (> 0.3 mag), `cubic_shape_miss` (z = 7 miss minus z = 3 miss > 0.18 mag,",
    "`cubic_misses_z3` (> 0.19 mag), `cubic_misses_z7` (> 0.5 mag), `cubic_shape_miss` (z = 7 miss minus z = 3 miss > 0.28 mag,")
