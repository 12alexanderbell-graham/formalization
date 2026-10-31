import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


sub("FINDINGS.md",
    "at Ω_m = 0.3[in] the printed l₀ is 0.685[✓F1_printedL0] instead of 3.115[✓F1_l0]",
    "at Ω_m = 0.7[in] the printed l₀ is 0.685[✓F1_printedL0] instead of 3.115[✓F1_l0]")
