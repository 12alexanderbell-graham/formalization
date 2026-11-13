"""Global part: mass curve up to x = 1e4 (and beyond) in homology variables, extrema, Lyapunov bound."""
import mpmath as mp
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import be_mass as B

mp.mp.dps = 30

# starting point x = 7 from the high-precision x-integration
u7, v7 = B.uv_x(mp.mpf(7))
xi1 = mp.findroot(lambda x: (lambda uv: uv[1] - 2 * uv[0])(B.uv_x(x)), mp.mpf('6.45'))
m1 = B.mass_x(xi1)
M1 = 4 * mp.pi * m1 ** 2          # 4 pi m1^2 = u v^3 at xi1

def V(u, v):
    return (u - 1 - mp.log(u)) + (v - 2 - 2 * mp.log(v / 2))

V7 = V(u7, v7)

# ---- Lyapunov: dV/dt = (1-1/u) u (3-u-v) + (1-2/v) v (u-1) = (u-1)(3-u-v) + (u-1)(v-2) = -(u-1)^2
# symbolic check at random points
import random
random.seed(1)
mxerr = 0
for _ in range(1000):
    u = mp.mpf(random.uniform(0.01, 5)); v = mp.mpf(random.uniform(0.01, 5))
    lhs = (1 - 1 / u) * u * (3 - u - v) + (1 - 2 / v) * v * (u - 1)
    mxerr = max(mxerr, abs(lhs + (u - 1) ** 2))
print('dV/dt + (u-1)^2 max abs over 1000 random points:', mp.nstr(mxerr, 5))

# max of u v^3 on {V <= c}: Lagrange condition 1/(u-1) = 3/(v-2), i.e. v = 3u - 1 (u>1); boundary V = c
c = V7
uu = mp.findroot(lambda u: V(u, 3 * u - 1) - c, mp.mpf('1.1'))
vv = 3 * uu - 1
Pmax = uu * vv ** 3
print('V(7) =', mp.nstr(V7, 15))
print('argmax on {V<=V7}: u =', mp.nstr(uu, 15), ' v =', mp.nstr(vv, 15))
print('max u v^3 on {V<=V7} =', mp.nstr(Pmax, 15), ' -> m bound =', mp.nstr(mp.sqrt(Pmax / (4 * mp.pi)), 15))
print('4 pi m1^2 =', mp.nstr(M1, 15), ' gap (4pi m1^2 - max) =', mp.nstr(M1 - Pmax, 10))
# brute-force check of the constrained max on a polar grid
best = 0
for k in range(20000):
    th = 2 * mp.pi * k / 20000
    # find r with V(1 + r cos, 2 + r sin) = c along ray
    def h(r):
        return V(1 + r * mp.cos(th), 2 + r * mp.sin(th)) - c
    # bracket
    lo, hi = mp.mpf(0), mp.mpf('0.01')
    while h(hi) < 0 and hi < 3:
        lo, hi = hi, hi * 1.5
    if h(hi) < 0:
        continue
    r = mp.findroot(h, (lo, hi), solver='bisect') if False else None
    # simple bisection
    for _ in range(60):
        mid = (lo + hi) / 2
        if h(mid) < 0: lo = mid
        else: hi = mid
    uq, vq = 1 + lo * mp.cos(th), 2 + lo * mp.sin(th)
    best = max(best, uq * vq ** 3)
    if k % 5000 == 0:
        pass
print('grid max u v^3 on boundary (20000 rays):', mp.nstr(best, 15))

# ---- trajectory from t = log 7 to t = log 1e6 with scipy DOP853 (float) and mpmath taylor (check)
def rhs(t, y):
    u, v = y
    return [u * (3 - u - v), v * (u - 1)]

t7 = float(mp.log(7))
tend = float(mp.log(mp.mpf(10) ** 6))
sol = solve_ivp(rhs, (t7, tend), [float(u7), float(v7)], method='DOP853', rtol=1e-13, atol=1e-15,
                dense_output=True)
ts = np.linspace(t7, tend, 400001)
U, Vv = sol.sol(ts)
P = U * Vv ** 3
Vt = np.array([float(V(mp.mpf(a), mp.mpf(b))) for a, b in zip(U[::200], Vv[::200])])
print('V monotone non-increasing on sampled trajectory:', bool(np.all(np.diff(Vt) <= 1e-14)))
print('sup m on [7, 1e6] (sampled) =', np.sqrt(P.max() / (4 * np.pi)), ' at x =', np.exp(ts[P.argmax()]))

# extrema: d(uv^3)/dt = u v^3 (2u - v) -> roots of 2u - v
G = 2 * U - Vv
idx = np.where(np.sign(G[:-1]) != np.sign(G[1:]))[0]
f = lambda t: (lambda y: 2 * y[0] - y[1])(sol.sol(t))
mpm = lambda t: (lambda y: np.sqrt(y[0] * y[1] ** 3 / (4 * np.pi)))(sol.sol(t))
print('extrema of m for x in [7, 1e6] (type, x, m):')
for i in idx:
    tr = brentq(f, ts[i], ts[i + 1], xtol=1e-14)
    kind = 'max' if G[i] > 0 else 'min'
    print('  %s  x = %.10g   m = %.12f' % (kind, np.exp(tr), mpm(tr)))
print('m_inf = sqrt(2/pi) =', mp.nstr(mp.sqrt(2 / mp.pi), 15), ' m(1e6) =', mpm(tend))

# high-precision check of the trajectory and the first two extrema beyond 7 with mpmath taylor
F = mp.odefun(lambda t, y: [y[0] * (3 - y[0] - y[1]), y[1] * (y[0] - 1)], mp.log(7), [u7, v7])
for tguess in [np.log(22), np.log(100)]:
    pass
for i in idx[:4]:
    tr = brentq(f, ts[i], ts[i + 1], xtol=1e-14)
    trm = mp.findroot(lambda t: (lambda y: 2 * y[0] - y[1])(F(t)), mp.mpf(tr))
    y = F(trm)
    print('  mp check: x = %s  m = %s' % (mp.nstr(mp.exp(trm), 15), mp.nstr(mp.sqrt(y[0] * y[1] ** 3 / (4 * mp.pi)), 18)))
y = F(mp.log(mp.mpf(10) ** 4))
print('mp: x=1e4  u,v =', mp.nstr(y[0], 15), mp.nstr(y[1], 15), ' m =', mp.nstr(mp.sqrt(y[0] * y[1] ** 3 / (4 * mp.pi)), 15),
      ' V =', mp.nstr(V(y[0], y[1]), 10))
yf = sol.sol(np.log(1e4))
print('scipy: x=1e4 u,v =', yf, ' m =', np.sqrt(yf[0] * yf[1] ** 3 / (4 * np.pi)))
