#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "STATE.md"
s = p.read_text(encoding="utf-8")
old = "(see the Blasius section: f''(0) ∈ [0.33205733621519, 0.33205733621520] for every solution; a solution exists)."
new = ("(see the Blasius section: f''(0) ∈ [0.33205733621519, 0.33205733621520] for every solution; a solution exists; "
       "the whole velocity profile f'(η) and the displacement thickness are certified to the same fourteen digits).")
assert s.count(old) == 1
p.write_text(s.replace(old, new), encoding="utf-8")
