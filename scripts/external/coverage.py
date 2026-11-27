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
    """Reading theorems, and (run 2026-11-27T0628Z, target R) reading `def X : Prop` declarations,
    with their namespace prefix (`namespace ReaderA` ... `end ReaderA`)."""
    src = open(path, encoding='utf-8').read()
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    src = re.sub(r'--[^\n]*', '', src)
    out, ns = [], []
    for line in src.splitlines():
        m = re.match(r'\s*namespace\s+([\w.]+)', line)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r'\s*end\s+([\w.]+)\s*$', line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        m = (re.match(r'\s*theorem\s+([A-Za-z_][\w.\']*)', line)
             or re.match(r'\s*def\s+([A-Za-z_][\w.\']*)\s*:\s*Prop\b', line))
        if m:
            out.append(['.'.join(ns + [m.group(1)]), line.lstrip().startswith('theorem'), line + '\n'])
        elif out:
            out[-1][2] += line + '\n'
    # A reader's theorem WITH a complete proof (no `sorry`) is the reader's own lemma (e.g. that a
    # series converges, so a `tsum` is not a junk 0: target O, run 2026-11-27T0628Z), not a claim
    # of the source; only `sorry`'d theorems and `Prop` definitions are claims to close.
    return [n for n, is_thm, body in out if not is_thm or re.search(r'\bsorry\b', body)]


def closure_mentions(path):
    """Names a closure relates to a frozen statement: `type_of% @X`, or a fully qualified reading
    name used in the statement of a closure theorem (`theorem t : ReaderA.ReadingRH ↔ ...`)."""
    src = open(path, encoding='utf-8').read()
    # `type_of% @X.{u}` (universe-polymorphic reading, run 2026-11-27T0628Z sunflower): the capture
    # must not keep the trailing `.` before the universe list.
    used = set(m.rstrip('.') for m in re.findall(r'type_of%\s*@([\w.\']+)', src))
    for st in re.findall(r'^theorem\s+[\w.\']+\s*(.*?):=', src, flags=re.M | re.S):
        if 'Frozen.' in st:
            used |= set(re.findall(r'[A-Za-z_][\w\']*\.[\w.\']+', st))
    return used


def main():
    reading, closures = sys.argv[1], sys.argv[2:]
    names = theorems(reading)
    used = set()
    for c in closures:
        used |= closure_mentions(c)
    unc = 0
    for n in names:
        hit = any(u == n or u.endswith('.' + n) for u in used) if '.' not in n else n in used
        print(f"{'closed   ' if hit else 'UNCOVERED'}  {n}")
        unc += not hit
    print(f'# {len(names) - unc}/{len(names)} reading theorems closed')
    sys.exit(1 if unc else 0)


if __name__ == '__main__':
    main()
