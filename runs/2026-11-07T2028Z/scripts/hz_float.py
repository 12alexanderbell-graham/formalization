#!/usr/bin/env python3
"""Run 2026-11-07T2028Z: float study of the Hiemenz (Falkner-Skan beta=1) shooting problem
f''' + f f'' + 1 - f'^2 = 0, f(0)=f'(0)=0, f''(0)=a: the shooting value a*, event times for
a* -/+ d, and the variational growth along the solution."""
import mpmath as mp
mp.mp.dps = 40
def F(t, y): return [y[1], y[2], -y[0]*y[2] - 1 + y[1]**2]
def shoot(a, L=12):
    sol = mp.odefun(F, 0, [mp.mpf(0), mp.mpf(0), a])
    return sol
def classify(a, L=12, dt=mp.mpf(1)/20):
    sol = mp.odefun(F, 0, [mp.mpf(0), mp.mpf(0), mp.mpf(a)])
    t = mp.mpf(0)
    while t < L:
        t += dt
        y = sol(t)
        if y[1] > 1: return 'over', float(t), [float(v) for v in y]
        if y[2] < 0: return 'under', float(t), [float(v) for v in y]
    return 'none', float(t), [float(v) for v in sol(t)]
lo, hi = mp.mpf('1.2'), mp.mpf('1.3')
for _ in range(45):
    mid = (lo+hi)/2
    c = classify(mid)[0]
    if c == 'over': hi = mid
    elif c == 'under': lo = mid
    else: print('none at', mid); break
print('a* in', mp.nstr(lo, 20), mp.nstr(hi, 20))
for d in ['1e-6','1e-8','1e-10','1e-12']:
    for s in (-1, 1):
        a = (lo+hi)/2 + s*mp.mpf(d)
        print(d, s, classify(a, L=15))
