#!/usr/bin/env python3
"""Run 2026-11-26T1228Z: float scan (not evidence): separation (q(0) = 0) with suction F(0) = C on the scaled field
F''' = -K F F'' + 1 - F'^2; shooting on K (over for K above the value, slow below), events as SBase.SlowS / Over."""
from scipy.integrate import solve_ivp
def cls(K, C, L=14):
    s = solve_ivp(lambda t, y: [y[1], y[2], -K*y[0]*y[2] + 1 - y[1]**2], [0, L], [C, 0, 0], max_step=0.01, rtol=1e-11, atol=1e-13)
    t, y = s.t, s.y
    for i in range(1, len(t)):
        if y[1][i] > 1: return 'over', t[i]
        if 0 <= y[1][i] and y[2][i] < 3*(1-y[1][i]) and y[0][i] > 11/15 and t[i] > 0.05: return 'slow', t[i]
    return 'none', None
for C in (0.0, 0.01, 0.02, 0.05):
    lo, hi = 4.0, 6.0
    for _ in range(45):
        m = (lo+hi)/2
        if cls(m, C)[0] == 'over': hi = m
        else: lo = m
    print(f'C={C}: K*={lo:.7f} beta*={-1/lo:.7f}', cls(lo*0.99, C), cls(lo*1.01, C))
