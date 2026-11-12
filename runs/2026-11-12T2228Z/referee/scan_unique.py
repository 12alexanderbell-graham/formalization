#!/usr/bin/env python3
"""Referee: uniqueness scan of F(s)=p(L;s)-1 over s<0 (L=15 and L=20), plus profile checks at the root
(min/max of p, q/(1-p) growth = fast approach)."""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from fs_taylor import integrate, solve, F
mp.mp.dps = 30
h = mp.mpf('0.25'); N = 22
res = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rows_referee.json')))
grid = [mp.mpf(-2000 + 50 * i) / 1000 for i in range(30)] + [mp.mpf(-5000 + 25 * i) / 10000 for i in range(200)]
grid = sorted(set(grid))
for b100 in [-4, -5, -6, -7, -8, -9, -11, -12, -13, -14, -16]:
    beta = mp.mpf(b100) / 100
    line = [str(b100)]
    for L in (15, 20):
        vals = [F(beta, s, L, mp.mpf('0.5'), 20) for s in grid]
        ch = []
        for i in range(len(grid) - 1):
            a, b = vals[i], vals[i + 1]
            if a is None and b is None: continue
            if (a is None) != (b is None):
                ch.append(('blowup-edge', float(grid[i]), float(grid[i + 1]))); continue
            if a * b < 0: ch.append(('root', float(grid[i]), float(grid[i + 1])))
        nblow = sum(v is None for v in vals)
        line.append('L=%d: %s; blowups=%d (largest blowing-up s=%s)' % (L, ch, nblow,
                    max([float(s) for s, v in zip(grid, vals) if v is None], default=None)))
    s = mp.mpf(res[str(b100)]['best'])
    r, (pmin, pmax, traj) = integrate(beta, s, 20, h, N, record=True)
    rat = {int(t): mp.nstr(q / (1 - p), 6) for t, f, p, q in traj if t in (4, 6, 8, 10) and 1 - p > 0}
    pmin_val = min(p for _, _, p, _ in traj)
    pmax_10 = max(p for t, _, p, _ in traj if t <= 10)
    line.append('profile: min p=%s, max p(eta<=10)=%s, q/(1-p) at eta=4,6,8,10: %s' %
                (mp.nstr(pmin_val, 8), mp.nstr(pmax_10, 15), rat))
    print('\n  '.join(line), flush=True)
