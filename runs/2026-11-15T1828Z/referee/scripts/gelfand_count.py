"""Referee check: radial solutions of the Gelfand problem in the unit ball of R^3.

W solves W'' + (2/s) W' + e^W = 0, W(0) = 0, W'(0) = 0.  lambda(s) = s^2 e^{W(s)}.
Radial solutions for parameter lam <-> radii s > 0 with lambda(s) = lam.
With t = log s, v = log lambda = W + 2t:  v'' + v' - 2 + e^v = 0 (autonomous).
Stage 1: integrate in s from a series start to s = 1.  Stage 2: integrate v in t.
"""
import sys
import numpy as np
from scipy.integrate import solve_ivp

RT, AT = 1e-13, 1e-15

# Stage 1: series W = -s^2/6 + s^4/120 - s^6/1890 + ...  (start at s0 small)
s0 = 1e-3
W0 = -s0**2 / 6 + s0**4 / 120 - s0**6 / 1890
dW0 = -s0 / 3 + s0**3 / 30 - 6 * s0**5 / 1890


def f_s(s, y):
    W, dW = y
    return [dW, -2.0 / s * dW - np.exp(W)]


r1 = solve_ivp(f_s, [s0, 1.0], [W0, dW0], method="DOP853", rtol=RT, atol=AT)
W1, dW1 = r1.y[:, -1]
# v = W + 2t, v_t = s W' + 2
v1, vt1 = W1 + 0.0, 1.0 * dW1 + 2.0


def f_t(t, y):
    v, vt = y
    return [vt, 2.0 - vt - np.exp(v)]


def ev_turn(t, y):
    return y[1]


T_MAX = float(sys.argv[1]) if len(sys.argv) > 1 else np.log(1e12)
r2 = solve_ivp(f_t, [0.0, T_MAX], [v1, vt1], method="DOP853", rtol=RT, atol=AT,
               events=ev_turn, dense_output=True)
zt = r2.t_events[0]
zv = r2.y_events[0][:, 0]
print(f"integrated to s = {np.exp(T_MAX):.3e}; {len(zt)} turning points found")
for k in range(min(8, len(zt))):
    kind = "max" if k % 2 == 0 else "min"
    print(f"  zeta_{k} = {np.exp(zt[k]):.10f}   lambda(zeta_{k}) = {np.exp(zv[k]):.10f} ({kind})")
print(f"  last: zeta_{len(zt)-1} = {np.exp(zt[-1]):.4e}, lambda = {np.exp(zv[-1]):.12f}")

# Monotone pieces: [0, zeta_0], [zeta_0, zeta_1], ... ; lambda(0) = 0.
ends_t = np.concatenate([[-np.inf], zt, [T_MAX]])
ends_v = np.concatenate([[-np.inf], zv, [r2.y[0, -1]]])


def count(lam):
    L = np.log(lam)
    n = 0
    roots = []
    for a, b, va, vb in zip(ends_t[:-1], ends_t[1:], ends_v[:-1], ends_v[1:]):
        lo, hi = min(va, vb), max(va, vb)
        if lo < L < hi or L == vb:  # strictly inside piece, or hits right end
            n += 1
            if np.isfinite(a) and n <= 6:
                # bisection on dense output for the radius
                x0, x1 = a, b
                for _ in range(200):
                    m = 0.5 * (x0 + x1)
                    if (r2.sol(m)[0] - L) * (r2.sol(x0)[0] - L) <= 0:
                        x1 = m
                    else:
                        x0 = m
                roots.append(np.exp(0.5 * (x0 + x1)))
            elif not np.isfinite(a):
                roots.append("in (0, zeta_0)")
    return n, roots


for lam in [2.0, 2.05, 2.5, 3.3, 3.321992117, 1.95, 1.9, 1.5, 1.0]:
    n, roots = count(lam)
    rs = ", ".join(r if isinstance(r, str) else f"{r:.6f}" for r in roots)
    print(f"lambda = {lam}: {n} radii with s <= {np.exp(T_MAX):.1e}   first: {rs}")

print(f"count drops to one below lambda(zeta_1) = {np.exp(zv[1]):.10f}")
print(f"min over all computed minima: {np.exp(zv[1::2].min()):.10f}; "
      f"max over maxima k>=2: {np.exp(zv[2::2].max()):.10f}")
