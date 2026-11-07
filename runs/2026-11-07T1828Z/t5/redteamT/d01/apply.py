#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
s = p.read_text(encoding="utf-8")
old = "(0.56[✓F8_sizes] % at z = 1, 6.7[✓F8_sizes] % at z = 2)"
new = "(6.7[✓F8_sizes] % at z = 1, 0.56[✓F8_sizes] % at z = 2)"
assert s.count(old) == 1
p.write_text(s.replace(old, new), encoding="utf-8")
