#!/usr/bin/env python3
"""Run 2026-11-27T0028Z (float scan, not evidence): wall conditions 4 (f(0) = 0) and 5 (p(0) = 0) of the statement
that the printed reversed-flow wall shear -0.005158 at beta = -0.1988 overshoots. A witness keeps q(0) = -0.005158 and
moves f(0) = c (or p(0) = w) to the value at which the solution no longer overshoots (the decaying reversed-flow
solution). Classify on [0, 30]: 'over' (p > 1 somewhere), 'under' (p < 1 throughout, falling away from one)."""
import numpy as np
from scipy.integrate import solve_ivp
B = -0.1988; Q0 = -0.005158
def cls(c, w, L=30):
    rhs = lambda t, y: [y[1], y[2], -y[0]*y[2] - B*(1 - y[1]**2)]
    ev = lambda t, y: y[1] - 1.0; ev.terminal = True; ev.direction = 1
    s = solve_ivp(rhs, [0, L], [c, w, Q0], max_step=0.01, rtol=1e-11, atol=1e-13, events=ev)
    if s.t_events[0].size: return 'over', s.t_events[0][0]
    return 'under', s.y[1][-1]
def bis(par):
    lo, hi = -0.05, 0.05
    a = cls(*par(lo))[0]; b = cls(*par(hi))[0]
    print('ends', lo, a, hi, b)
    if a == b: return None
    for _ in range(45):
        m = (lo + hi) / 2
        if cls(*par(m))[0] == a: lo = m
        else: hi = m
    return lo, hi
print('base (0, 0):', cls(0, 0))
print('f(0) = c:', bis(lambda x: (x, 0)))
print('p(0) = w:', bis(lambda x: (0, x)))
