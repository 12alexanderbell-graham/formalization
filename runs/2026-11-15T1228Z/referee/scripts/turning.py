"""Referee computation: turning points of lambda(s) = s^2 e^{w(s)},
w'' + (2/s) w' + e^w = 0, w(0)=0, w'(0)=0.

Method A: scipy DOP853 on the autonomous system in t = log s,
   x = log lambda = w + 2t, y = s*phi:  x' = 2 + y, y' = -y - e^x.
   Turning points = zeros of y + 2 (lambda' = s e^w (2 - v), v = -y).
Method B: mpmath odefun (Taylor, 30 digits) on the homology system
   u' = u(3-u-v), v' = v(u-1) in t, turning points = zeros of v - 2,
   lambda = u v.  Roots refined by findroot.
"""
import numpy as np
from scipy.integrate import solve_ivp
import mpmath as mp

# series w = -s^2/6 + s^4/120 - s^6/1890 + 61 s^8/1632960
def series(s):
    w = -s**2/6 + s**4/120 - s**6/1890 + 61*s**8/1632960
    p = -s/3 + s**3/30 - 6*s**5/1890 + 8*61*s**7/1632960
    return w, p

# ---------------- Method A ----------------
s0 = 1e-4
w0, p0 = series(s0)
t0 = np.log(s0)
X0 = [w0 + 2*t0, s0*p0]
def f(t, z):
    x, y = z
    return [2 + y, -y - np.exp(x)]
ev = lambda t, z: z[1] + 2
T1 = np.log(1e8)
sol = solve_ivp(f, (t0, T1), X0, method='DOP853', rtol=1e-14, atol=1e-16,
                events=ev, dense_output=True)
print("Method A (scipy DOP853):")
tz = sol.t_events[0]
for k, (t, z) in enumerate(zip(tz, sol.y_events[0])):
    print(f"  k={k}  zeta={np.exp(t):.12g}  lambda={np.exp(z[0]):.12g}")
# dense check of sign of lambda' (= sign of 2+y) on fine grid
tt = np.linspace(t0, T1, 2_000_001)
yy = sol.sol(tt)[1] + 2
sc = np.nonzero(np.diff(np.sign(yy)))[0]
print("  sign changes of 2-v on grid:", len(sc), " min |y+2| away from roots:",
      end=" ")
mask = np.ones_like(yy, bool)
for i in sc:
    mask[max(0, i-200):i+200] = False
print(np.min(np.abs(yy[mask & (tt > t0 + 1)])))
# local extrema of y+2 between roots (would reveal tangential near-misses)
d = np.diff(yy)
ext = np.nonzero(np.diff(np.sign(d)))[0] + 1
print("  |y+2| at its local extrema:", [f"{abs(yy[i]):.3g}" for i in ext[:12]])

# ---------------- Method B ----------------
mp.mp.dps = 30
s0m = mp.mpf('1e-4')
w, p = series(s0m)
u0 = s0m*mp.e**w/(-p); v0 = -s0m*p
tb0 = mp.log(s0m)
F = mp.odefun(lambda t, z: [z[0]*(3 - z[0] - z[1]), z[1]*(z[0] - 1)], tb0, [u0, v0])
print("Method B (mpmath odefun Taylor, 30 digits):")
# scan for sign changes of v-2 on a grid in t, then refine
grid = [tb0 + mp.mpf(i)/50 for i in range(int((mp.log(2e6) - tb0)*50))]
prev = None; roots = []
for t in grid:
    val = F(t)[1] - 2
    if prev is not None and mp.sign(val) != mp.sign(prev[1]):
        r = mp.findroot(lambda tt: F(tt)[1] - 2, (prev[0], t), solver='anderson')
        roots.append(r)
    prev = (t, val)
for k, r in enumerate(roots):
    uu, vv = F(r)
    print(f"  k={k}  zeta={mp.nstr(mp.e**r, 18)}  lambda={mp.nstr(uu*vv, 18)}"
          f"  u-1={mp.nstr(uu-1, 5)}  v'={mp.nstr(vv*(uu-1), 5)}")
