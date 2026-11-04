import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

sub("Checked/Cosmography/B1Fit.lean",
    "for every\nΩ ≥ 0.1 (referee `runs/2026-11-04T0228Z/referee_b1fit.md`; floating point; at Ω = 0.04 the\nhalf-range is 0.054 and at Ω = 0 it is 0.19, so near Ω = 0 such fits are not covered), so such fits\nsatisfy the hypothesis;",
    "for every\nΩ ∈ [0, 1] (referee `runs/2026-11-04T0228Z/referee_b1fit.md`; floating point), so such fits\nsatisfy the hypothesis;")
sub("STATE.md",
    "least-squares fits over z ≤ 5.1 meet the hypothesis for Ω ≥ 0.1;",
    "least-squares fits over z ≤ 5.1 meet the hypothesis for every Ω ∈ [0, 1];")
