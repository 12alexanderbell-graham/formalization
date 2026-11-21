"""Referee computation: turning points of lambda = s^2 e^W for the regular solution of
W'' + (2/s) W' + e^W = 0, W(0)=0.  Taylor series of W at the centre up to s0, then a
high-order Taylor method for the homology system in t = log s:
    u' = u(3 - u - v),  v' = v(u - 1),   u = s e^W / (-W'),  v = -s W'.
Turning points: zeros of v - 2; lambda = u v = 2u there.
Usage: python3 turning.py DPS ORDER STEP
"""
import sys
from mpmath import mp, mpf, exp, log

dps, N, h = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
mp.dps = dps
h = mpf(h)
s0 = mpf('0.5')

# --- series of W at s = 0 ---
M = 160
c = [mpf(0)] * (M + 3)   # W coefficients
e = [mpf(0)] * (M + 3)   # e^W coefficients
e[0] = mpf(1)
for n in range(M):
    # c_{n+2} (n+2)(n+3) = -e_n
    c[n + 2] = -e[n] / ((n + 2) * (n + 3))
    # (n+1) e_{n+1} = sum_{k=0}^{n} (k+1) c_{k+1} e_{n-k}
    e[n + 1] = sum((k + 1) * c[k + 1] * e[n - k] for k in range(n + 1)) / (n + 1)
W = sum(c[n] * s0**n for n in range(M + 1))
Wp = sum(n * c[n] * s0**(n - 1) for n in range(1, M + 1))
tail = abs(c[M] * s0**M)
u = s0 * exp(W) / (-Wp)
v = -s0 * Wp
t = log(s0)


def taylor(u0, v0):
    U = [u0] + [mpf(0)] * N
    V = [v0] + [mpf(0)] * N
    for n in range(N):
        UU = sum(U[k] * U[n - k] for k in range(n + 1))
        UV = sum(U[k] * V[n - k] for k in range(n + 1))
        U[n + 1] = (3 * U[n] - UU - UV) / (n + 1)
        V[n + 1] = (UV - V[n]) / (n + 1)
    return U, V


def ev(P, x):
    r = mpf(0)
    for a in reversed(P):
        r = r * x + a
    return r


def dev(P, x):
    r = mpf(0)
    for k in range(len(P) - 1, 0, -1):
        r = r * x + k * P[k]
    return r


roots = []
tend = mpf(16)
while t < tend and len(roots) < 7:
    U, V = taylor(u, v)
    un, vn = ev(U, h), ev(V, h)
    if (v - 2) * (vn - 2) < 0:
        # Newton on Taylor polynomial within the step
        x = h * (2 - v) / (vn - v)
        for _ in range(100):
            dx = (ev(V, x) - 2) / dev(V, x)
            x -= dx
            if abs(dx) < mpf(10) ** (-dps + 5):
                break
        roots.append((t + x, 2 * ev(U, x)))
    u, v, t = un, vn, t + h

print('series tail at s0:', mp.nstr(tail, 3))
for k, (tz, lam) in enumerate(roots):
    print(k, 'zeta =', mp.nstr(exp(tz), 40), ' lambda =', mp.nstr(lam, 40))
