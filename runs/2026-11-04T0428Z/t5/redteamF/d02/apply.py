import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

f = "Checked/Fidelity/MaxwellSpec.lean"
sub(f, "  /-- (c) NEAR MISS. Liquid root paired with the middle (unstable) root. -/",
    "  /-- (c) NEAR MISS. Liquid root paired with the middle (unstable) root: rejected because coexistence requires both phases to be mechanically stable, (∂p/∂v)_T < 0 at `vl` and `vg`, which fails at the middle root. -/")
sub(f, "  /-- (c) NEAR MISS. Middle (unstable) root paired with the gas root. -/",
    "  /-- (c) NEAR MISS. Middle (unstable) root paired with the gas root: rejected because coexistence requires both phases to be mechanically stable, (∂p/∂v)_T < 0 at `vl` and `vg`, which fails at the middle root. -/")
sub(f, "vanishes, `∫_{vl}^{vg} p dv = ps (vg - vl)`.\n",
    "vanishes, `∫_{vl}^{vg} p dv = ps (vg - vl)`. Both phases must also be mechanically stable,\n(∂p/∂v)_T < 0 at `vl` and at `vg`; the spec rejects every pair with an endpoint on the unstable branch.\n")
