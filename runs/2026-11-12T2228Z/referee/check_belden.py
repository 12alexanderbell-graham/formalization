#!/usr/bin/env python3
"""Referee: re-check the Belden et al. (arXiv:1907.09912v1 p.4) printed kappa values, and probe the extra
F-sign change found near the blow-up edge at L=20 for beta=-0.05 (is it a genuine solution?)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from fs_taylor import F, solve, integrate
mp.mp.dps = 50
for b, a, c, Ls in [('-0.02', '-0.066', '-0.064', [30, 40]), ('0.5', '0.92', '0.93', [10, 15]),
                    ('0', '0.46', '0.47', [12, 15]), ('-0.12', '0.28', '0.285', [15, 20])]:
    for L in Ls:
        s = solve(mp.mpf(b), mp.mpf(a), mp.mpf(c), L, mp.mpf('0.125'), 34)
        print(b, L, mp.nstr(s, 22), flush=True)
mp.mp.dps = 30
beta = mp.mpf('-0.05')
for L in (20, 22, 25):
    vals = [(s, F(beta, s, L, mp.mpf('0.25'), 22)) for s in [mp.mpf(-1475 + 5 * i) / 10000 for i in range(11)]]
    print('beta=-0.05 L=%d' % L, [(float(s), None if v is None else float(v)) for s, v in vals], flush=True)
