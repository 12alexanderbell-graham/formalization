#!/usr/bin/env python3
"""Run 2026-11-27T0028Z (float scan, not evidence): hypothesis 8 (q > 0 after the wall) of the separation statements.
The solution from f(0) = p(0) = q(0) = 0 of f''' + f f'' + beta(1 - f'^2) = 0 is fixed by beta alone; a witness needs a
beta >= -0.1988376 whose solution has p -> 1 with the fast approach while q < 0 somewhere. Scan beta and print the
behaviour on [0, 20]: max p, min q, p and q at the end."""
import numpy as np
from scipy.integrate import solve_ivp
def run(b, L=20):
    def rhs(t, y): return [y[1], y[2], -y[0]*y[2] - b*(1 - y[1]**2)]
    ev = lambda t, y: abs(y[1]) - 50; ev.terminal = True
    s = solve_ivp(rhs, [0, L], [0, 0, 0], max_step=0.01, rtol=1e-10, atol=1e-12, events=ev)
    return s
for b in list(np.linspace(-0.19883, -0.15, 6)) + list(np.linspace(-0.15, 2.0, 44)):
    s = run(b); p, q = s.y[1], s.y[2]
    print(f'beta={b:+.5f} tend={s.t[-1]:5.2f} maxp={p.max():+.4f} minq={q[1:].min():+.4f} end p={p[-1]:+.4f} q={q[-1]:+.3e}')

# bisection between p -> -inf (beta = 0.65) and p -> +inf (beta = 0.70)
import sys
if len(sys.argv) > 1:
    lo, hi = 0.65, 0.70
    sgn = lambda b: run(b, 30).y[1][-1] > 1
    for _ in range(45):
        m = (lo + hi) / 2
        if sgn(m): hi = m
        else: lo = m
    print('boundary beta in', lo, hi)
    for b in (lo, hi):
        s = run(b, 30); p, q, f = s.y[1], s.y[2], s.y[0]
        for t in (1, 2, 3, 4, 5, 6, 8, 10):
            i = np.searchsorted(s.t, t)
            if i < len(s.t): print(f'  b={b:.12f} t={s.t[i]:.2f} f={f[i]:+.5f} p={p[i]:+.6f} q={q[i]:+.6f}')

# overshoot-and-return zero-shear solutions below the separation value: bisect on the sign of p(12) - 1
if len(sys.argv) > 1 and sys.argv[1] == 'over':
    for lo, hi in ((-1.36, -1.26), (-2.42, -2.32)):
        side = lambda b: run(b, 12).y[1][-1] > 1
        slo = side(lo)
        for _ in range(40):
            m = (lo + hi) / 2
            if side(m) == slo: lo = m
            else: hi = m
        s = run(lo, 12); p, q = s.y[1], s.y[2]
        i1 = np.argmax(p > 1)
        print(f'beta*={lo:.10f}: max p {p.max():.4f} at {s.t[p.argmax()]:.2f}, min q {q.min():.4f} at {s.t[q.argmin()]:.2f}, '
              f'p > 1 from {s.t[i1]:.2f}, p(8)={p[np.searchsorted(s.t, 8)]:.8f}, q(8)={q[np.searchsorted(s.t, 8)]:.2e}, '
              f'q < 0 on ({s.t[np.argmax(q < 0)]:.2f}, ...)')
