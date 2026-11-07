import numpy as np
from scipy.integrate import solve_ivp
def F(t, y): return [y[1], y[2], -y[0]*y[2] - 1 + y[1]**2]
def ev_over(t, y): return y[1] - 1
ev_over.terminal = True; ev_over.direction = 1
def ev_under(t, y): return y[2]
ev_under.terminal = True; ev_under.direction = -1
def cls(a, L=15):
    s = solve_ivp(F, [0, L], [0, 0, a], rtol=1e-13, atol=1e-15, method='DOP853', events=[ev_over, ev_under])
    if s.t_events[0].size: return 'over', s.t_events[0][0]
    if s.t_events[1].size: return 'under', s.t_events[1][0]
    return 'none', s.t[-1]
lo, hi = 1.2, 1.3
for _ in range(60):
    m = (lo+hi)/2
    c = cls(m)[0]
    if c == 'over': hi = m
    elif c == 'under': lo = m
    else: break
print(repr(lo), repr(hi))
for d in [1e-4, 1e-6, 1e-8, 1e-10]:
    print(d, cls(lo - d), cls(hi + d))
print('---')
for a in [1.2325876568, 1.2325876569]:
    for L in [6.5, 7, 7.5, 8]:
        s = solve_ivp(F, [0, L], [0, 0, a], rtol=1e-13, atol=1e-16, method='DOP853', dense_output=True)
        ts = np.linspace(0, L, 4001); Y = s.sol(ts)
        print(a, L, s.y[:, -1], 'max p', Y[1].max(), 'min q', Y[2].min(), cls(a, 12))
