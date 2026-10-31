import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")

# FINDINGS.md F1 plain-words numeric example: digits transposed in the "correct" value (3.115 -> 3.151)
sub("FINDINGS.md",
    "the printed l₀ is 0.685 instead of 3.115",
    "the printed l₀ is 0.685 instead of 3.151")
