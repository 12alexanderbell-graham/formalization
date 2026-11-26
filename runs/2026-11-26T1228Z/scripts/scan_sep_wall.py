#!/usr/bin/env python3
"""Run 2026-11-26T1228Z: float scan (not evidence): separation (q(0) = 0) with a moving wall F'(0) = P0 on the scaled
field F''' = -K F F'' + 1 - F'^2 from (0, P0, 0); shooting value K* (over below, slow above), events as SBase."""
from scipy.integrate import solve_ivp
def cls(K, P0, L=14):
    s = solve_ivp(lambda t, y: [y[1], y[2], -K*y[0]*y[2] + 1 - y[1]**2], [0, L], [0, P0, 0], max_step=0.01, rtol=1e-11, atol=1e-13)
    t, y = s.t, s.y
    for i in range(1, len(t)):
        if y[1][i] > 1: return 'over'
        if 0 <= y[1][i] and y[2][i] < 3*(1-y[1][i]) and y[0][i] > 11/15 and t[i] > 0.05: return 'slow'
    return 'none'
for P0 in (0.0, 0.001, 0.002, 0.005):
    lo, hi = 4.8, 5.3
    for _ in range(30):
        m = (lo+hi)/2
        if cls(m, P0) == 'over': lo = m
        else: hi = m
    print(f'P0={P0}: K*={hi:.6f} beta*={-1/hi:.7f}')
