"""Independent referee computation for the first minimum of the Bonnor-Ebert mass.
Equation: w'' + (2/s) w' + e^w = 0, w(0)=0, phi = w'.
m(s) = s^2 (-phi) e^{w/2} / sqrt(4 pi);  contrast e^{-w}.
Variables t = log s, z = w + 2t:  z'' + z' - 2 + e^z = 0 (autonomous damped oscillator);
s^2 e^w = e^z, s*phi = z' - 2, 4 pi m^2 = (z'-2)^2 e^z.
Critical points of m: e^w = phi^2/2  <=>  e^z = (z'-2)^2/2.
Method A: mpmath power series at 0 + mpmath odefun (Taylor) in t, dps 30.
Method B: scipy DOP853 in (w, phi) in s, rtol 1e-14, series start.
Method C: scipy DOP853 in homology (u, v) in t.
"""
import sys
import numpy as np
import mpmath as mp
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

mp.mp.dps = 30

def series_coeffs(N):
    # w = sum a_k s^{2k}, e^w = sum b_k s^{2k}
    a = [mp.mpf(0)] * (N + 1); b = [mp.mpf(0)] * (N + 1)
    b[0] = mp.mpf(1)
    for n in range(N):
        a[n + 1] = -b[n] / ((2 * n + 2) * (2 * n + 3))
        b[n + 1] = sum((k * a[k] * b[n + 1 - k]) for k in range(1, n + 2)) / (n + 1)
    return a

A = series_coeffs(80)
def w_series(s):
    s = mp.mpf(s)
    return sum(A[k] * s ** (2 * k) for k in range(len(A)))
def phi_series(s):
    s = mp.mpf(s)
    return sum(2 * k * A[k] * s ** (2 * k - 1) for k in range(1, len(A)))

s0 = mp.mpf('0.5')
# check series truncation
print('series tail term at 0.5:', mp.nstr(A[-1] * s0 ** 160, 5))
t0 = mp.log(s0)
z0 = w_series(s0) + 2 * t0
zp0 = s0 * phi_series(s0) + 2

# ---------------- Method A: mpmath odefun -----------------
F = mp.odefun(lambda t, y: [y[1], 2 - y[1] - mp.exp(y[0])], t0, [z0, zp0])
def mA(t):
    z, zp = F(t)
    return mp.sqrt((zp - 2) ** 2 * mp.exp(z) / (4 * mp.pi))
def gA(t):
    z, zp = F(t)
    return mp.exp(z) - (zp - 2) ** 2 / 2
def report_A(sguess, label):
    tr = mp.findroot(gA, mp.log(sguess), tol=mp.mpf(10) ** -26)
    z, zp = F(tr)
    s = mp.exp(tr); w = z - 2 * tr
    print(f'[A] {label}: xi = {mp.nstr(s, 18)}  m = {mp.nstr(mA(tr), 18)}  contrast e^-w = {mp.nstr(mp.exp(-w), 18)}')
    return s, mA(tr), mp.exp(-w)

xi1A, m1A, c1A = report_A(6.45, 'xi1 (max)')
xi2A, m2A, c2A = report_A(67.0, 'xi2 (min)')
# value at s = 150 in homology variables
t150 = mp.log(150)
z, zp = F(t150)
v150 = -(zp - 2)            # v = -s phi
u150 = mp.exp(z) / v150     # u = s e^w / (-phi) = s^2 e^w / (-s phi)
V150 = (u150 - 1 - mp.log(u150)) + (v150 - 2 - 2 * mp.log(v150 / 2))
print(f'[A] at s=150: u = {mp.nstr(u150, 15)} v = {mp.nstr(v150, 15)} V = {mp.nstr(V150, 15)}  m(150) = {mp.nstr(mA(t150), 15)}')
sys.stdout.flush()

# ---------------- Method B: scipy (w, phi) in s -----------------
def rhs_s(s, y):
    w, p = y
    return [p, -2 * p / s - np.exp(w)]
sB0 = 0.5
yB0 = [float(w_series(sB0)), float(phi_series(sB0))]
solB = solve_ivp(rhs_s, [sB0, 200.0], yB0, method='DOP853', rtol=1e-14, atol=1e-16, dense_output=True)
def gB(s):
    w, p = solB.sol(s); return np.exp(w) - p * p / 2
def mB(s):
    w, p = solB.sol(s); return s * s * (-p) * np.exp(w / 2) / np.sqrt(4 * np.pi)
for lo, hi, lab in [(6, 7, 'xi1'), (60, 75, 'xi2')]:
    r = brentq(gB, lo, hi, xtol=1e-15, rtol=1e-15)
    w, p = solB.sol(r)
    print(f'[B] {lab}: xi = {r:.13f}  m = {mB(r):.13f}  contrast = {np.exp(-w):.10f}')

# ---------------- Method C: homology (u, v) in t, out to 1e5 and beyond --------------
def rhs_uv(t, y):
    u, v = y
    return [u * (3 - u - v), v * (u - 1)]
tC0 = float(t0)
vC0 = float(-s0 * phi_series(s0)); uC0 = float(s0 * mp.exp(w_series(s0)) / (-phi_series(s0)))
tend = np.log(1e7)
solC = solve_ivp(rhs_uv, [tC0, tend], [uC0, vC0], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True)
tt = np.linspace(tC0, tend, 400001)
U, Vv = solC.sol(tt)
M = np.sqrt(U * Vv ** 3 / (4 * np.pi))
# extrema: sign changes of u - v/2
g = U - Vv / 2
idx = np.where(np.sign(g[:-1]) != np.sign(g[1:]))[0]
ext = []
for i in idx:
    f = lambda t: (lambda y: y[0] - y[1] / 2)(solC.sol(t))
    tr = brentq(f, tt[i], tt[i + 1], xtol=1e-14)
    u, v = solC.sol(tr)
    ext.append((np.exp(tr), np.sqrt(u * v ** 3 / (4 * np.pi))))
print('[C] extrema of m (xi, m), first 12 and up to 1e7:')
for k, (s, m) in enumerate(ext):
    if k < 12 or s > 1e4:
        print(f'   {"max" if k % 2 == 0 else "min"} {k}: xi = {s:.8g}  m = {m:.12f}')
print('[C] number of extrema up to 1e7:', len(ext))
print('[C] limit sqrt(2/pi) =', np.sqrt(2 / np.pi), ' m(1e5) =', float(np.sqrt(np.prod(solC.sol(np.log(1e5)) * np.array([1, 0])+0) )) if False else '')
u5, v5 = solC.sol(np.log(1e5)); print('[C] m(1e5) =', np.sqrt(u5 * v5 ** 3 / (4 * np.pi)), ' m(1e7)=', M[-1])
m2 = ext[1][1]; xi2 = ext[1][0]; xi1 = ext[0][0]
# smallest gap inf_{xi >= xi1, |xi - xi2| >= 1} m - m(xi2): on grid + refine near boundaries
S = np.exp(tt)
mask = (S >= xi1) & (np.abs(S - xi2) >= 1)
j = np.argmin(M[mask])
print(f'[C] gap: min over xi>=xi1,|xi-xi2|>=1 of m = {M[mask][j]:.12f} at xi = {S[mask][j]:.6f}; gap = {M[mask][j] - m2:.6e}')
for sb in [xi2 - 1, xi2 + 1]:
    u, v = solC.sol(np.log(sb)); print(f'    m({sb:.4f}) - m(xi2) = {np.sqrt(u*v**3/(4*np.pi)) - m2:.6e}')
# later minima relative to m2
print('[C] second minimum minus first:', ext[3][1] - m2)

# Lyapunov check: min of u v^3 on {V <= V150}
Vf = lambda u, v: (u - 1 - np.log(u)) + (v - 2 - 2 * np.log(v / 2))
uh, vh = solC.sol(np.log(150.0))
V150C = Vf(uh, vh)
print(f'[C] at s=150: u = {uh:.12f} v = {vh:.12f} V = {V150C:.12f}')
# along t, V must be nonincreasing
Vt = Vf(U, Vv)
print('[C] V monotone nonincreasing on grid (tol 1e-12):', bool(np.all(np.diff(Vt) <= 1e-12)))
