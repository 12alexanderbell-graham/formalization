"""Method A: scipy DOP853 directly in (xi, w, phi), plus homology-variable (u,v) check and Volterra bound."""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, minimize_scalar

SQ = np.sqrt(4 * np.pi)


def rhs(s, y):
    w, p = y
    return [p, -2 / s * p - np.exp(w)]


s0 = 1e-3
w0 = -s0**2 / 6 + s0**4 / 120
p0 = -s0 / 3 + s0**3 / 30


def m_of(s, y):
    return s**2 * (-y[1]) * np.exp(y[0] / 2) / SQ


def dm(s, y):  # sign of d m/ds  ~ 2u - v
    w, p = y
    v = -s * p
    u = s * np.exp(w) / (-p)
    return 2 * u - v


dm.terminal = False
sol = solve_ivp(rhs, (s0, 1e6), [w0, p0], method='DOP853', rtol=1e-13, atol=1e-16,
                dense_output=True, events=dm)
print('DOP853 (xi variables) extrema:')
for s, y in zip(sol.t_events[0], sol.y_events[0]):
    print('  xi=%.12f m=%.12f contrast=%.6f' % (s, m_of(s, y), np.exp(-y[0])))
D = sol.sol
mf = lambda s: m_of(s, D(s))
xi2, xi3 = sol.t_events[0][1], sol.t_events[0][2]
m3 = mf(xi3)
# sup over [xi2, 1e6] \ (xi3-1, xi3+1): dense grid in log + refine
grid = np.concatenate([np.linspace(xi2, xi3 - 1, 20000), np.linspace(xi3 + 1, 1e6, 200000),
                       np.geomspace(xi3 + 1, 1e6, 200000)])
mv = np.array([mf(s) for s in grid])
i = np.argmax(mv)
print('m(xi3)=%.12f; m(xi3-1)=%.12f m(xi3+1)=%.12f' % (m3, mf(xi3 - 1), mf(xi3 + 1)))
print('sup over grid of [xi2,1e6] minus (xi3-1,xi3+1): %.12f at xi=%.4f; gap m3-sup=%.3e' % (mv[i], grid[i], m3 - mv[i]))
print('sup over [2000,1e6] grid: %.12f' % max(mf(s) for s in np.geomspace(2000, 1e6, 100000)))
print('min over [xi1, 1e6] grid vs m(xi2): %.12f vs %.12f' % (min(mf(s) for s in np.geomspace(sol.t_events[0][0], 1e6, 100000)), mf(xi2)))


# homology variables from xi=1 (u,v known from solution), t = log xi
def hom(t, y):
    u, v = y
    return [u * (3 - u - v), v * (u - 1)]


w1, p1 = D(1.0)
u1, v1 = np.exp(w1) / (-p1), -p1
def ev2(t, y):
    return 2 * y[0] - y[1]
hs = solve_ivp(hom, (0, np.log(1e6)), [u1, v1], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True, events=ev2)
print('homology-variable extrema:')
for t, y in zip(hs.t_events[0], hs.y_events[0]):
    print('  xi=%.12f m=%.12f' % (np.exp(t), np.sqrt(y[0] * y[1]**3 / (4 * np.pi))))
uv = hs.sol(np.log(2000))
V = lambda u, v: (u - 1 - np.log(u)) + (v - 2 - 2 * np.log(v / 2))
V2000 = V(*uv)
print('xi=2000: u=%.15f v=%.15f V=%.12e' % (uv[0], uv[1], V2000))
w2, p2 = D(2000.0)
print('  (xi-variables) u=%.15f v=%.15f V=%.12e' % (2000 * np.exp(w2) / (-p2), -2000 * p2, V(2000 * np.exp(w2) / (-p2), -2000 * p2)))
# max of u v^3 on {V <= V2000}: log(uv^3) = log u + 3 log v is concave-ish; max on boundary.
# parametrize boundary by angle: for each direction solve V(1+r cos, 2+r sin)=V2000
best = 0
for th in np.linspace(0, 2 * np.pi, 200001):
    f = lambda r: V(1 + r * np.cos(th), 2 + r * np.sin(th)) - V2000
    rmax = 0.5
    r = brentq(f, 0, rmax)
    u, v = 1 + r * np.cos(th), 2 + r * np.sin(th)
    best = max(best, u * v**3)
print('max u v^3 on {V<=V(2000)} = %.12f ; 4 pi m(xi3)^2 = %.12f ; ratio %.6f' % (best, 4 * np.pi * m3**2, best / (4 * np.pi * m3**2)))
print('implied m bound for xi>=2000: %.12f' % np.sqrt(best / (4 * np.pi)))
