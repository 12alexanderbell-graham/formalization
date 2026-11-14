#!/usr/bin/env python3
"""Which candidate certified values would collide with numbers in FINDINGS.md author prose (check_numbers G1/G5)?

Run 2026-11-14T0628Z: a new record's certified values are compared with every decimal, signed integer (or integer
after = / ≈) and exactly-terminating fraction in the author prose of the whole verified section, not only its own
finding (G1 compares absolute values, G5 fractions signed). Certifying 3, 6, 0.25 in de Sitter collided with
"−3", "−6H₀²", "Ω = 0.25" in F1, F9, F10 notes. Pick the witness model so that no value collides.

  python3 runs/2026-11-14T0628Z/scripts/prose_collisions.py -2.8333 0.4167 1.25
"""
import re
import sys
from decimal import Decimal as D

sys.path.insert(0, "scripts/trust")
import check_numbers as C  # noqa: E402

text = open("FINDINGS.md").read()
prose, _ = C.strip_blocks(C.scope(text))
absv, fr = set(), set()
for line in prose.split("\n"):
    s = C.code_blank(line)
    for t in re.finditer(r"(?<![\w.])(" + C.NUM + r")(?!\d)(?!\.\d)", s):
        num = t.group(1)
        if not ("." in num or "×10" in num):
            if not (C.norm(num).startswith("-") or s[:t.start()].rstrip().endswith(("≈", "≃", "=", "~"))):
                continue
        absv.add(abs(C.value(num)[0]))
    for m in re.finditer(r"(?<![\w.])(" + C.FRAC + r")(?![\d/])", line):
        a, b = C.norm(m.group(1)).replace(" ", "").split("/")
        if int(b):
            fr.add(D(int(a)) / D(int(b)))
bad = [x for x in sys.argv[1:] if abs(D(x)) in absv or D(x) in fr]
print("collisions:", bad or "none")
sys.exit(1 if bad else 0)
