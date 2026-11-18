"""Independent referee computation: Lambda(s) = s^2 exp(W(s)), W'' + (2/s) W' + e^W = 0, W(0)=0, W'(0)=0.
Variable t = ln s, y = W + 2t = ln Lambda:  y'' + y' - 2 + e^y = 0.
Extrema of Lambda <=> y' = 0.  Two independent integrators (scipy DOP853 and mpmath Taylor odefun)."""
import numpy as np
from scipy.integrate import solve_ivp
import mpmath as mp

s0 = 1e-4
W0 = -s0**2/6 + s0**4/120
Ws0 = -s0/3 + s0**3/30
t0 = np.log(s0)
y0 = [W0 + 2*t0, s0*Ws0 + 2]

def f(t, z):
    return [z[1], 2 - np.exp(z[0]) - z[1]]

def ev(t, z): return z[1]
ev.direction = 0

T = np.log(1e9)
res = {}
for rtol in (1e-12, 1e-13):
    sol = solve_ivp(f, (t0, T), y0, method='DOP853', rtol=rtol, atol=1e-15, events=ev, dense_output=True)
    ext = [(np.exp(t), np.exp(z[0])) for t, z in zip(sol.t_events[0], sol.y_events[0])]
    res[rtol] = (sol, ext)
    print(f"rtol={rtol}: {len(ext)} extrema up to s=1e9")
    for k, (s, L) in enumerate(ext[:12]):
        print(f"  zeta_{k} = {s:.12g}   Lambda = {L:.12f}   Lambda-2 = {L-2:+.3e}")

sol, ext = res[1e-13]

# mpmath cross-check of first 6 extrema
mp.mp.dps = 25
def fm(t, z): return [z[1], 2 - mp.e**z[0] - z[1]]
s0m = mp.mpf('1e-4'); t0m = mp.log(s0m)
Fm = mp.odefun(fm, t0m, [(-s0m**2/6 + s0m**4/120) + 2*t0m, s0m*(-s0m/3 + s0m**3/30) + 2])
print("mpmath check:")
for k, (s, L) in enumerate(ext[:6]):
    tz = mp.findroot(lambda t: Fm(t)[1], mp.log(s))
    print(f"  zeta_{k} = {mp.nstr(mp.e**tz, 15)}  Lambda = {mp.nstr(mp.e**Fm(tz)[0], 15)}")

# root counting of Lambda(s) = lam for s in (0, 1e9]
ts = np.linspace(t0, T, 400001)
Y = sol.sol(ts)[0]
lext = [L for _, L in ext]
print("N(lam):")
for lam in (0.5, 1.6, 1.7, 1.9, 2.05, 2.1, 2.2, 3.0, 3.32, 3.33):
    d = Y - np.log(lam)
    n = int(np.sum(np.sign(d[:-1]) != np.sign(d[1:])))
    # tail: last extrema pair beyond which Lambda stays inside (Lambda(zeta_odd), Lambda(zeta_even))
    # by the Extrema facts; settled when lam lies outside that window
    j = len(lext) - 2
    lo, hi = sorted(lext[j:j+2])
    settled = not (lo <= lam <= hi)
    print(f"  lam={lam}: roots on (0,1e9] = {n}; tail window [{lo:.6f},{hi:.6f}] -> settled={settled}")
