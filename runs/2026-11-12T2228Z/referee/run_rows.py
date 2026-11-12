#!/usr/bin/env python3
"""Referee: reversed-branch f''(0) for the 11 rows, convergence in L, step h and order N."""
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from fs_taylor import integrate, solve, F

mp.mp.dps = 40
rows = {-4: ('-0.0966367875', '-0.0966367874'), -5: ('-0.1082710833', '-0.1082710832'),
        -6: ('-0.1179241111', '-0.1179241110'), -7: ('-0.1258585318', '-0.1258585317'),
        -8: ('-0.1322276544', '-0.1322276543'), -9: ('-0.1371138119', '-0.1371138118'),
        -11: ('-0.1425079104', '-0.1425079103'), -12: ('-0.1429351944', '-0.1429351943'),
        -13: ('-0.1417095022', '-0.1417095021'), -14: ('-0.1386389253', '-0.1386389252'),
        -16: ('-0.1255676643', '-0.1255676642')}
Ls = [int(x) for x in (sys.argv[1].split(',') if len(sys.argv) > 1 else '10,15,20,25,30'.split(','))]
out = {}
for b100, (lo, hi) in rows.items():
    beta = mp.mpf(b100) / 100
    # independent bracket: coarse scan of F on s in [-0.30, -0.01] at L=12 for the negative root
    grid = [mp.mpf(-300 + 2 * i) / 1000 for i in range(146)]
    vals = [F(beta, s, 12, mp.mpf('0.25'), 20) for s in grid]
    roots = [(grid[i], grid[i + 1]) for i in range(len(grid) - 1)
             if vals[i] is not None and vals[i + 1] is not None and vals[i] * vals[i + 1] < 0]
    assert len(roots) == 1, (b100, roots)
    a, b = roots[0]
    res = {}
    for L in Ls:
        t = time.time()
        sA = solve(beta, a, b, L, mp.mpf('0.25'), 26)
        res[L] = sA
        a, b = sA - mp.mpf('1e-6'), sA + mp.mpf('1e-6')
        print(b100, L, mp.nstr(sA, 22), '%.1fs' % (time.time() - t), flush=True)
    Lmax = Ls[-1]
    # discretisation check at Lmax: halve step, raise order
    sB = solve(beta, a, b, Lmax, mp.mpf('0.125'), 32)
    best = res[Lmax]
    marg = min(best - mp.mpf(lo), mp.mpf(hi) - best)
    out[b100] = dict(byL={str(L): mp.nstr(v, 25) for L, v in res.items()}, h_check=mp.nstr(sB, 25),
                     disc_diff=mp.nstr(abs(sB - best), 3), best=mp.nstr(best, 20),
                     in_window=bool(mp.mpf(lo) < best < mp.mpf(hi)), margin=mp.nstr(marg, 6))
    print(b100, 'h/2,N32:', mp.nstr(sB, 22), 'margin', mp.nstr(marg, 6), 'in', out[b100]['in_window'], flush=True)
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rows_referee.json'), 'w'), indent=1)
