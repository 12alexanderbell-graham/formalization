"""Independent referee computation for the Bonnor-Ebert count.

Isothermal equation w'' + (2/s) w' + e^w = 0, w(0)=0, w'(0)=0.
Log form: t = ln s, u = w + 2t, v = du/dt:  u' = v, v' = 2 - v - e^u  (autonomous).
m(s) = s^2 (-w') e^{w/2}/sqrt(4 pi) = (2 - v) e^{u/2} / sqrt(4 pi).
Extrema of m in t: e^u = (2 - v)^2 / 2.
Cross-check: s-form integration (w, phi) directly for the first extrema.
"""
import numpy as np
from scipy.integrate import solve_ivp

C = 1.0 / np.sqrt(4 * np.pi)
SIS = np.sqrt(2 / np.pi)

def series(s):
    # w = -s^2/6 + s^4/120 - 61 s^6/45360 + ...  (standard isothermal series, psi = -w)
    w = -s**2 / 6 + s**4 / 120 - 61 * s**6 / 45360
    dw = -s / 3 + s**3 / 30 - 61 * s**5 / 7560
    return w, dw

def rhs_t(t, y):
    u, v = y
    return [v, 2 - v - np.exp(u)]

def m_t(y):
    return (2 - y[1]) * np.exp(y[0] / 2) * C

def ev(t, y):
    return np.exp(y[0]) - (2 - y[1]) ** 2 / 2

s0 = 1e-3
w0, dw0 = series(s0)
t0 = np.log(s0)
y0 = [w0 + 2 * t0, s0 * dw0 + 2]
TMAX = np.log(1e13)

def run(rtol):
    return solve_ivp(rhs_t, (t0, TMAX), y0, method="DOP853", rtol=rtol, atol=1e-15,
                     events=ev, dense_output=True)

sol = run(1e-13)
sol2 = run(1e-11)
ext = [(np.exp(t), m_t(y)) for t, y in zip(sol.t_events[0], sol.y_events[0])]
ext2 = [(np.exp(t), m_t(y)) for t, y in zip(sol2.t_events[0], sol2.y_events[0])]
print("extrema (s, m) with rtol 1e-13; diff to rtol 1e-11")
for k, ((s, m), (s2, m2)) in enumerate(zip(ext, ext2)):
    if k > 9: break
    print(f"k={k}: xi={s:.10g}  m={m:.12f}  m-sqrt(2/pi)={m - SIS:+.3e}  dm={m - m2:.1e} dxi/xi={(s - s2)/s:.1e}")
print("sqrt(2/pi) =", SIS)

# s-form cross-check of first extrema
def rhs_s(s, y):
    w, p = y
    return [p, -2 / s * p - np.exp(w)]
def ms(s, y):
    return s**2 * (-y[1]) * np.exp(y[0] / 2) * C
def evs(s, y):  # dm/ds = 0  <=>  2 p + s(-2p/s - e^w) ... compute directly
    w, p = y
    dp = -2 / s * p - np.exp(w)
    return 2 * s * (-p) + s**2 * (-dp) + s**2 * (-p) * p / 2
ss = solve_ivp(rhs_s, (s0, 1e5), [w0, dw0], method="DOP853", rtol=1e-13, atol=1e-16, events=evs)
print("s-form check:", [(f"{s:.9g}", f"{ms(s, y):.10f}") for s, y in zip(ss.t_events[0], ss.y_events[0])])

# Root counts: sign changes of m - mu on a fine t-grid, plus tail argument via extrema values
tg = np.linspace(t0, TMAX, 4_000_001)
mg = m_t(sol.sol(tg))
mus = [0.5, 0.7, 0.75, 0.79, 0.7975, 0.80, 0.81, 0.9, 1.18, 1.19]
vals = [m for _, m in ext]
print("\nN(mu): grid sign changes on s in (1e-3, 1e13]; segment count from extrema")
for mu in mus:
    d = mg - mu
    nz = np.sum(np.sign(d[:-1]) * np.sign(d[1:]) < 0)
    # segment count: [0, xi0] then each [xi_j, xi_{j+1}] with mu strictly between
    seg = int(0 < mu < vals[0])
    for a, b in zip(vals[:-1], vals[1:]):
        seg += int(min(a, b) < mu < max(a, b))
    last_s = np.exp(tg[:-1][np.sign(d[:-1]) * np.sign(d[1:]) < 0][-1]) if nz else None
    print(f"mu={mu}: grid={nz}, segments={seg}, largest root s~{last_s and f'{last_s:.4g}'}, |mu-sqrt(2/pi)|={abs(mu-SIS):.2e}")
