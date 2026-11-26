#!/usr/bin/env python3
"""Run 2026-11-26T1828Z, part 1 plan (float, not evidence): receding wall F'(0) = -d for the scaled separation field
F''' = -K F F'' + 1 - F'^2 from (0, -d, 0). Shooting value K*, events as SBase (over: p > 1; slow: 0 <= p, q < 3(1-p),
f > 11/15), and the quantities the unclamping needs: the time p stays negative, min f, max q, and the energy bound
q^2/2 <= E(0) - min_{p in [-d,1]} (p^3/3 - p - 2K d p) with E = q^2/2 + p^3/3 - p - 2K d p (non-increasing while
f >= -d and 0 <= q <= 2)."""
from scipy.integrate import solve_ivp
def run(K, d, L=14):
    s = solve_ivp(lambda t, y: [y[1], y[2], -K*y[0]*y[2] + 1 - y[1]**2], [0, L], [0, -d, 0], max_step=0.005, rtol=1e-11, atol=1e-13)
    return s.t, s.y
def cls(K, d):
    t, y = run(K, d)
    for i in range(1, len(t)):
        if y[1][i] > 1: return 'over', t[i]
        if 0 <= y[1][i] and y[2][i] < 3*(1-y[1][i]) and y[0][i] > 11/15 and t[i] > 0.05: return 'slow', t[i]
    return 'none', None
for d in (1/500, 1/200):
    lo, hi = 4.9, 5.3
    for _ in range(40):
        m = (lo+hi)/2
        if cls(m, d)[0] == 'over': lo = m
        else: hi = m
    print(f'd={d}: K*={hi:.7f} beta*={-1/hi:.8f}')
d = 1/200
for K in (5.100, 5.101, 5.1015, 5.103):
    c, te = cls(K, d)
    t, y = run(K, d, te if te else 14)
    tneg = max((t[i] for i in range(len(t)) if y[1][i] < 0), default=0)
    E0 = -d**3/3 + d + 2*K*d*d
    pmin = min(p**3/3 - p - 2*K*d*p for p in [-d + i*(1+d)/10000 for i in range(10001)])
    print(f'K={K}: {c} at {te}, beta={-1/K:.6f}, p<0 until {tneg:.4f}, min f {min(y[0]):.6f}, max q {max(y[2]):.4f}, energy bound q <= {(2*(E0-pmin))**0.5:.4f}')
