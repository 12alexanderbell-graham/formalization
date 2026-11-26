#!/usr/bin/env python3
"""Coverage of a blind reading by closures (external test; run 2026-11-26T1529Z).

  python3 scripts/external/coverage.py <reading.lean> <closure.lean> [<closure.lean> ...]

Every `theorem` of the blind reading is a claim of the source as a blind reader rendered it. A closure
file proves, about the frozen (outside) statement, `(type_of% @Frozen) ↔ (type_of% @Reading)` or
`→`. This script lists each reading theorem and whether some closure theorem mentions it with
`type_of% @<name>` (closed) or not (UNCOVERED: the outside Lean statement says nothing about that claim,
or nobody has related them yet). Exit status 1 if any theorem is uncovered, so a verdict cannot be DONE
while a claim of the source has no closure. Why: the human survey of OpenAI's release (arXiv 2610.17090)
found family 159's Lean statement covers the corollary (Erdős 3) but not the headline quantitative bound;
this check turns "the headline has no counterpart" into a mechanical, listed result.
"""
import re
import sys


def theorems(path):
    src = open(path, encoding='utf-8').read()
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    return re.findall(r'^\s*theorem\s+([A-Za-z_][\w.\']*)', src, flags=re.M)


def main():
    reading, closures = sys.argv[1], sys.argv[2:]
    names = theorems(reading)
    used = set()
    for c in closures:
        used |= set(re.findall(r'type_of%\s*@([\w.\']+)', open(c, encoding='utf-8').read()))
    unc = 0
    for n in names:
        hit = any(u == n or u.endswith('.' + n) for u in used)
        print(f"{'closed   ' if hit else 'UNCOVERED'}  {n}")
        unc += not hit
    print(f'# {len(names) - unc}/{len(names)} reading theorems closed')
    sys.exit(1 if unc else 0)


if __name__ == '__main__':
    main()
