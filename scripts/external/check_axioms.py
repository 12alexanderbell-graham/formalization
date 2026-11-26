#!/usr/bin/env python3
"""Check `#print axioms` output (possibly wrapped over several lines by Lean's pretty printer, as for
long names: run 2026-11-26T1529Z, T2 job 140090067980) against the standard three.

  python3 check_axioms.py <log file>   -> exit 0 iff every reported list is within the allowed set
                                            and at least one list was found
"""
import re
import sys
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
txt = open(sys.argv[1], encoding='utf-8').read()
found = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", txt, flags=re.S)
none = re.findall(r"'([^']+)' does not depend on any axioms", txt)
bad = []
for name, lst in found:
    ax = {a.strip() for a in lst.replace('\n', ' ').split(',') if a.strip()}
    if not ax <= ALLOWED:
        bad.append((name, sorted(ax - ALLOWED)))
for name, extra in bad:
    print(f'NON-STANDARD AXIOMS {name}: {extra}')
print(f'axioms: {len(found)} lists checked, {len(none)} declarations without axioms, {len(bad)} non-standard')
sys.exit(1 if bad or not (found or none) else 0)
