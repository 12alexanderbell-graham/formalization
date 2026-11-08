#!/usr/bin/env python3
import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new), encoding="utf-8")
sub("scripts/trust/phrases.txt", 'its integral from {vl} to {vg} equals {ps} times the volume difference', 'its integral from {vl} to {vg} exceeds {ps} times the volume difference')
p = root / "LEDGER.md"
t = p.read_text(encoding="utf-8")
if not t.endswith("\n"):
    t += "\n"
t += '- 2026-11-08, run 2026-11-08T2228Z — **Phrase wording, part 4 (clarity; no statement, number or citation changed).** The phrase of `IsMaxwellCoexistence` uses the verb of the equal-area comparison ("exceeds").' + "\n"
p.write_text(t, encoding="utf-8")
