"""Independent double-precision check: homology system in t = log s,
u' = u(3 - u - v), v' = v(u - 1), lambda = u v, turning points at v = 2.
Initial data from the small-s expansion w = -s^2/6 + s^4/120 - ... (series computed in floats)."""
import numpy as np
from scipy.integrate import solve_ivp

# series of w at 0 (floats), same recurrence a_{n+1} = -e_{n-1}/((n+1)(n+2))
N = 30
a = [0.0] * (N + 2); e = [0.0] * (N + 2); e[0] = 1.0
for n in range(1, N + 1):
    a[n + 1] = -e[n - 1] / ((n + 1) * (n + 2))
    e[n] = sum(k * a[k] * e[n - k] for k in range(1, n + 1)) / n
s0 = 0.01
w = sum(a[k] * s0 ** k for k in range(N + 1))
wp = sum(k * a[k] * s0 ** (k - 1) for k in range(1, N + 1))
u0 = s0 * np.exp(w) / (-wp); v0 = -s0 * wp

def f(t, y):
    u, v = y
    return [u * (3 - u - v), v * (u - 1)]

def ev(t, y): return y[1] - 2
ev.direction = 0
sol = solve_ivp(f, [np.log(s0), np.log(2e5)], [u0, v0], method='DOP853', rtol=1e-14, atol=1e-16,
                events=ev, dense_output=True)
for i, (t, y) in enumerate(zip(sol.t_events[0], sol.y_events[0])):
    print(i, repr(np.exp(t)), repr(y[0] * y[1]))
