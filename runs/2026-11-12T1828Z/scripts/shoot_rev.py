# Run 2026-11-12T1828Z: float shooting for the reversed-flow Falkner–Skan branch, scaled form
# g''' = -K g g'' + 1 - g'^2, g(0)=g'(0)=0, g''(0)=A (K = 1/|beta|), physical f''(0) = A/sqrt(K).
# Classifies A: 'over' (g' > 1 somewhere) vs 'under' (g'' < 0 with g' > 0.3, falls back). Bisects the
# reversed-branch boundary in A < 0.
import sys, numpy as np
from scipy.integrate import solve_ivp
from fractions import Fraction as Fr
def cls(K, A, L=14):
    ev1 = lambda t, y: y[1] - 1; ev1.terminal = True
    ev2 = lambda t, y: y[2] if y[1] > 0.3 else 1.0; ev2.terminal = True; ev2.direction = -1
    s = solve_ivp(lambda t, y: [y[1], y[2], -K*y[0]*y[2] + 1 - y[1]**2], [0, L], [0, 0, A],
                  rtol=1e-13, atol=1e-15, events=[ev1, ev2], method='DOP853')
    if s.t_events[0].size: return 'over'
    if s.t_events[1].size: return 'under'
    return 'none'
def bisect(K, a, b, n=60):
    ca = cls(K, a); cb = cls(K, b); assert ca != cb, (a, ca, b, cb)
    for _ in range(n):
        m = (a + b) / 2
        if cls(K, m) == ca: a = m
        else: b = m
    return a, b, ca, cb
if __name__ == '__main__':
    for Ks in sys.argv[1:]:
        K = float(Fr(Ks))
        grid = np.linspace(-0.5, 0.0, 101)
        cs = [cls(K, A) for A in grid]
        for i in range(len(grid) - 1):
            if cs[i] != cs[i+1]:
                a, b, ca, cb = bisect(K, grid[i], grid[i+1])
                print(Ks, 'A in', repr(a), repr(b), ca, cb, 'q0 =', a / np.sqrt(K), flush=True)
