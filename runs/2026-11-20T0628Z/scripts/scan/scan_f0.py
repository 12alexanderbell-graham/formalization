# Float scan (not evidence): Falkner-Skan f''' + f f'' + beta (1 - f'^2) = 0 with p(0) = 0 and free f(0) = f0.
# For each f0, find wall shears q0 whose solution has p -> 1 (sign changes of p(L) - 1 along a q0 grid, L = 8),
# and report solutions whose shear is <= 0 somewhere (a witness shape for hypothesis 6 of fs_monotone_of_limit).
import numpy as np
from scipy.integrate import solve_ivp
import sys
beta = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
L = 8.0
def rhs(t, y):
    f, p, q = y
    return [p, q, -f * q - beta * (1 - p * p)]
def blow(t, y): return 50 - abs(y[1])
blow.terminal = True
def endp(f0, q0):
    s = solve_ivp(rhs, [0, L], [f0, 0.0, q0], rtol=1e-9, atol=1e-11, events=blow)
    if s.status == 1: return np.sign(s.y[1, -1]) * 50, s
    return s.y[1, -1], s
for f0 in np.linspace(-4, 4, 17):
    qs = np.linspace(-6, 6, 241)
    vals = [endp(f0, q)[0] - 1 for q in qs]
    for i in range(len(qs) - 1):
        if np.sign(vals[i]) != np.sign(vals[i + 1]) and abs(vals[i]) < 40 and abs(vals[i+1]) < 40:
            a, b = qs[i], qs[i + 1]
            for _ in range(50):
                m = (a + b) / 2
                if np.sign(endp(f0, m)[0] - 1) == np.sign(endp(f0, a)[0] - 1): a = m
                else: b = m
            v, s = endp(f0, a)
            print(f"f0={f0:+.2f} q0={a:+.6f} minq={s.y[2].min():+.4f} minp={s.y[1].min():+.4f} p(L)={s.y[1,-1]:.4f}")
