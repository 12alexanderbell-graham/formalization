import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


sub("FINDINGS.md",
    "true 0.809[✓F2_toy], printed −0.906[✓F2_toy]",
    "true –0.809[✓F2_toy], printed −0.906[✓F2_toy]")
