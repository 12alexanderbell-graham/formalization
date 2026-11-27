#!/usr/bin/env python3
"""List every comparator challenge of a family, by the solution module's directory (run 2026-11-27T0628Z).

  python3 scripts/external/family_challenges.py <ComparatorChallenges dir> <solution module or prefix>

A family's challenges are all `ComparatorChallenges/*.json` whose `solution_module` shares the first three
components (`OAI.<Area>.<Family>`) with the given module. A coverage verdict ("the Lean has no statement of X")
must be made against this whole list: run 2026-11-27T0628Z first judged O20 and O21 against only the challenges
near its size threshold and wrongly reported the Mahler equality case and the Euclidean Ramsey Classification as
having no Lean statement.

SUPERSEDED for coverage verdicts by `family_map.py` (run 2026-11-27T1248Z): grouping by solution directory still
missed `CommutingDerivations` (O10) and `GrahamSpherical` (O21); the scope documents are the authoritative map.
"""
import glob
import json
import os
import sys

d, mod = sys.argv[1], sys.argv[2]
key = '.'.join(mod.split('.')[:3])
rows = []
for f in sorted(glob.glob(os.path.join(d, '*.json'))):
    j = json.load(open(f))
    if '.'.join(j['solution_module'].split('.')[:3]) == key:
        lean = f[:-5] + '.lean'
        n = sum(1 for _ in open(lean)) if os.path.exists(lean) else -1
        rows.append((os.path.basename(f)[:-5], n, j['solution_module'], ' '.join(j['theorem_names'])))
for r in rows:
    print('%-40s %4d lines  %s  %s' % r)
print('# %d challenge(s) in family %s' % (len(rows), key))
