#!/usr/bin/env python3
"""Run 2026-11-26T1228Z: float scan (not evidence) for hypothesis 13 (f2(0) = 0) of fs_neg_decay_max_shear.
Scaled clamped-free field F''' = -K F F'' + 1 - F'^2 from (C, 0, a). For each suction C find the shooting
value a*(C) (slow below, over above) and report whether slow wall values a with a/sqrt(K) above the attached
wall shear (K = 10: q(0) < 0.3192697599) and a <= 11/10 exist; print the slow-event data at a candidate."""
import math
from scipy.integrate import solve_ivp
K = 10.0
def run(C, a, L=12):
    f = lambda t, y: [y[1], y[2], -K*y[0]*y[2] + 1 - y[1]**2]
    s = solve_ivp(f, [0, L], [C, 0, a], max_step=0.01, rtol=1e-11, atol=1e-13)
    return s.t, s.y
def cls(C, a):
    t, y = run(C, a)
    for i in range(len(t)):
        if y[1][i] > 1: return 'over', t[i]
        if y[2][i] <= 0: return 'neg', t[i]
        if t[i] > 0 and 0 <= y[1][i] and y[2][i] < 3*(1-y[1][i]) and y[0][i] > 11/15: return 'slow', t[i]
    return 'none', None
aref = 0.3192697599*math.sqrt(K)
print('a_ref', aref)
for C in (0.02, 0.05, 0.1, 0.15, 0.2):
    lo, hi = 0.5, 1.6
    for _ in range(50):
        m = (lo+hi)/2
        if cls(C, m)[0] == 'over': hi = m
        else: lo = m
    print(f'C={C}: a*={lo:.6f}  f2(0)=sqrt(K)C={math.sqrt(K)*C:.4f} q2*(0)={lo/math.sqrt(K):.5f}', 'slow at 1.05:', cls(C, 1.05), 'at 1.04:', cls(C, 1.04))
