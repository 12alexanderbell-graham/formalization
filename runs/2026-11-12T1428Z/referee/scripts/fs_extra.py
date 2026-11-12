#!/usr/bin/env python3
"""Referee extras:
 (1) window margins from the 25-digit values of fs_mp.py;
 (2) beta = -0.1988 (Guo Table 8 / Ganapol Table 5 row) and the reversed (Stewartson) branch at each row;
 (3) neighbouring shots s = s* +- ds: do they give f' -> 1 with f'' > 0 but only ALGEBRAIC decay
     (i.e. is the decay hypothesis hdec non-vacuous / essential)?
 (4) conversion to Hartree's m-form f''' + ((m+1)/2) f f'' + m (1 - f'^2) = 0:
     m = beta/(2-beta), f_m''(0) = f''(0) / sqrt(2 - beta).
"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from mpmath import mp, mpf, nstr, sqrt
import fs_mp
import numpy as np
from scipy.integrate import solve_ivp

mp.dps = 40
fs_mp.ORDER = 30
fs_mp.H = mpf('0.2')

VALS = {  # from fs_mp.py, dps 40, L = 10..16, two (order, h) settings, all agree to 25 digits
    '-0.15': mpf('0.2163614056471114364439954'),
    '-0.18': mpf('0.1286362205960608462171505'),
    '-0.19': mpf('0.08569974405981683242701547'),
    '-0.195': mpf('0.05517182857713765475532619'),
    '-0.198': mpf('0.02509428362086446625833389'),
}
WIN = {'-0.15': ('0.2163614056', '0.2163614057'), '-0.18': ('0.1286362205', '0.1286362206'),
       '-0.19': ('0.0856997440', '0.0856997441'), '-0.195': ('0.0551718285', '0.0551718286'),
       '-0.198': ('0.0250942836', '0.0250942837')}

print('(1) margins')
for b, s in VALS.items():
    lo, hi = map(mpf, WIN[b])
    print(f"  beta={b:7s} s={nstr(s, 20)} in=({lo < s < hi}) lower margin={nstr(s - lo, 4)} upper margin={nstr(hi - s, 4)}")

print('(2) beta=-0.1988 attached, and reversed branch at each row (asymptotic BC, L=14)')
s = fs_mp.solve(mpf('-0.1988'), 14, '0.0052')
print(f"  beta=-0.1988 attached s={nstr(s, 20)}")
for b, s0 in [('-0.15', '-0.13'), ('-0.18', '-0.097'), ('-0.19', '-0.069'), ('-0.195', '-0.047'), ('-0.198', '-0.023')]:
    try:
        sr = fs_mp.solve(mpf(b), 16, s0)
        print(f"  beta={b:7s} reversed s={nstr(sr, 15)}")
    except Exception as e:  # noqa
        print(f"  beta={b:7s} reversed: no convergence from {s0} ({type(e).__name__})")

print('(3) neighbouring shots, double precision, eta to 200')
for b, sv in VALS.items():
    beta = float(b)
    for ds in (+1e-3, -1e-3, +1e-6, -1e-6):
        s0 = float(sv) + ds
        rhs = lambda t, y: [y[1], y[2], -y[0] * y[2] - beta * (1 - y[1] ** 2)]
        ev = lambda t, y: y[2]
        ev.terminal = True
        r = solve_ivp(rhs, (0, 200), [0, 0, s0], rtol=1e-11, atol=1e-14, events=ev, method='DOP853')
        if r.status == 1:
            print(f"  beta={b:7s} ds={ds:+.0e}: f''=0 at eta={r.t_events[0][0]:.3f}, f'={r.y_events[0][0][1]:.6f}")
        else:
            p, q = r.y[1, -1], r.y[2, -1]
            print(f"  beta={b:7s} ds={ds:+.0e}: f''>0 on [0,200]; 1-f'(200)={1 - p:.3e}, f''(200)/(1-f'(200))={q / (1 - p):.3e}")

print("(4) Hartree m-form: m = beta/(2-beta), f_m''(0) = f''(0)/sqrt(2-beta)")
for b, s in list(VALS.items()) + [('-0.1988', None)]:
    if s is None:
        continue
    beta = mpf(b)
    m = beta / (2 - beta)
    print(f"  beta={b:7s} m={nstr(m, 15)}  f_m''(0)={nstr(s / sqrt(2 - beta), 15)}")
