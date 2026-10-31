import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


sub("FINDINGS.md",
    "1.3[✓F8_sizes]×10⁻⁵ up to z = 2",
    "1.3[✓F8_sizes]×10⁻⁷ up to z = 2")
