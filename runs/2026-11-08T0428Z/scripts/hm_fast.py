"""Run 2026-11-08T0428Z: float study of the Homann axisymmetric stagnation-point flow
f''' + 2 f f'' + 1 - f'^2 = 0, f(0) = f'(0) = 0, f'(inf) = 1 (shooting on q = f''(0))."""
import numpy as np, sys
from scipy.integrate import solve_ivp
K = float(sys.argv[1]) if len(sys.argv) > 1 else 2.0
def F(t, y): return [y[1], y[2], -K*y[0]*y[2] - 1 + y[1]**2]
def ev_over(t, y): return y[1] - 1
ev_over.terminal = True; ev_over.direction = 1
def ev_under(t, y): return y[2]
ev_under.terminal = True; ev_under.direction = -1
def cls(a, L=15):
    s = solve_ivp(F, [0, L], [0, 0, a], rtol=1e-13, atol=1e-15, method='DOP853', events=[ev_over, ev_under])
    if s.t_events[0].size: return 'over', s.t_events[0][0]
    if s.t_events[1].size: return 'under', s.t_events[1][0]
    return 'none', s.t[-1]
lo, hi = 1.0, 1.6
for _ in range(60):
    m = (lo+hi)/2
    c = cls(m)[0]
    if c == 'over': hi = m
    elif c == 'under': lo = m
    else: break
print(repr(lo), repr(hi))
for d in [1e-4, 1e-6, 1e-8, 1e-10]:
    print(d, cls(lo - d), cls(hi + d))
