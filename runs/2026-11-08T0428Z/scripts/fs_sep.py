"""Run 2026-11-08T0428Z: float study for the next step — Falkner–Skan separation β*: with f''(0) = 0 fixed,
shoot β in f''' + f f'' + β(1 − f'²) = 0 and classify by the Hiemenz events (overshoot p > 1 with q > 0,
undershoot q < 0 with p < 1)."""
from scipy.integrate import solve_ivp
def cls(b, L=30):
    F = lambda t, y: [y[1], y[2], -y[0]*y[2] - b*(1 - y[1]**2)]
    ov = lambda t, y: y[1] - 1; ov.terminal = True; ov.direction = 1
    un = lambda t, y: y[2]; un.terminal = True; un.direction = -1
    s = solve_ivp(F, [0, L], [0, 0, 0], rtol=1e-13, atol=1e-15, method='DOP853', events=[ov, un])
    if s.t_events[0].size: return 'over', s.t_events[0][0]
    if s.t_events[1].size: return 'under', s.t_events[1][0]
    return 'none', s.y[:, -1]
for b in [-0.25, -0.2, -0.198, -0.19, -0.15]: print(b, cls(b))
lo, hi = -0.25, -0.15
clo = cls(lo)[0]
for _ in range(60):
    m = (lo + hi) / 2
    if cls(m)[0] == clo: lo = m
    else: hi = m
print(repr(lo), repr(hi), cls(lo - 1e-9), cls(hi + 1e-9))
