#!/usr/bin/env python3
"""Referee: reversed-branch f''(0) at the other beta printed by Ganapol Table 7 / Fazio Table 4 (cross-check of sources)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from fs_taylor import F, solve
mp.mp.dps = 40
for b in ['-0.01', '-0.02', '-0.025', '-0.03', '-0.10', '-0.15', '-0.17', '-0.18', '-0.19']:
    beta = mp.mpf(b)
    grid = [mp.mpf(-300 + 2 * i) / 1000 for i in range(149)]
    Lb = 25 if beta > -0.035 else 14
    vals = [F(beta, s, Lb, mp.mpf('0.25'), 20) for s in grid]
    roots = [(grid[i], grid[i + 1]) for i in range(len(grid) - 1)
             if vals[i] is not None and vals[i + 1] is not None and vals[i] * vals[i + 1] < 0]
    a, c = roots[0]
    out = []
    for L in ([20, 30, 40] if beta > -0.035 else [15, 20, 30]):
        s = solve(beta, a, c, L, mp.mpf('0.25'), 26); a, c = s - mp.mpf('1e-7'), s + mp.mpf('1e-7')
        out.append('L=%d %s' % (L, mp.nstr(s, 20)))
    print(b, 'roots', [(float(x), float(y)) for x, y in roots], ' | '.join(out), flush=True)
