import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
s = p.read_text(encoding="utf-8")
old = "−0.249ε, −0.032ε and −0.400ε, −0.0152ε"
assert s.count(old) == 1
s = s.replace(old, "−0.149ε, −0.032ε and −0.400ε, −0.0152ε")
p.write_text(s, encoding="utf-8")
