"""Generator prototype for contracting homology cells in log radius (run 2026-11-20T1628Z).
Checks every condition of Work.Math.GContract.CCProp in exact rationals (fractions.Fraction), and the link
Q(next start error) <= (1 + theta) B + (1 + 1/theta) Q(rounding) of GContract.Q_add_le, along the regular
isothermal solution from s0 to s1. Prints the per-cell constants and the final bound. Not yet emitting Lean.
Usage: python3 gen_ccells.py [s0 s1 h N]"""
import sys, math
from fractions import Fraction as Fr
import numpy as np
from scipy.integrate import solve_ivp

s0 = float(sys.argv[1]) if len(sys.argv) > 1 else 8579 / 20
s1 = float(sys.argv[2]) if len(sys.argv) > 2 else 50000.0
H = Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(1, 10)
N = int(sys.argv[4]) if len(sys.argv) > 4 else 14
DEN = 10 ** 16
r0 = 649 / 125000000  # max-norm radius of GLamChain's end box (run 1028Z)

def f(s, y):
    w, p = y
    return [p, -2 / s * p - math.exp(w)]
z = 1e-3
sol = solve_ivp(f, [z, s0], [-z * z / 6, -z / 3], method='DOP853', rtol=1e-13, atol=1e-15)
w, p = sol.y[:, -1]
u0, v0 = s0 * math.exp(w) / (-p), -s0 * p

def rnd(x): return Fr(round(x * DEN), DEN)
def taylor(u, v, n):  # float Taylor coefficients of u' = u(3-u-v), v' = v(u-1)
    U, V = [u], [v]
    for k in range(n):
        uu = sum(U[i] * U[k - i] for i in range(k + 1)); uv = sum(U[i] * V[k - i] for i in range(k + 1))
        U.append((3 * U[k] - uu - uv) / (k + 1)); V.append((uv - V[k]) / (k + 1))
    return U, V
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def psc(c, a): return [c * x for x in a]
def pmul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def pder(a): return [i * a[i] for i in range(1, len(a))]
def qabs(a, h): return sum(abs(c) * h ** i for i, c in enumerate(a))
def lo(a, h): return a[0] - h * qabs(a[1:], h)
def hi(a, h): return a[0] + h * qabs(a[1:], h)
def peval(a, h): return sum(c * h ** i for i, c in enumerate(a))
def Q(e1, e2): return Fr(3, 2) * e1 * e1 + e1 * e2 + e2 * e2
def corner(mu, a, b):
    m11 = Fr(3, 2) * mu - (9 - 6 * a - 2 * b) / 2; m12 = mu / 2 - (2 - 4 * a + b) / 4; m22 = mu - (a - 2) / 2
    return m11 >= 0 and m22 >= 0 and m12 * m12 <= m11 * m22
def up(x, d=10 ** 12): return Fr(math.ceil(x * d), d)  # round a positive bound up

theta = Fr(1, 1000)
kappa = Fr(1, 100)
cu, cv = rnd(u0), rnd(v0)
delta = up(3.5 * r0 * r0 * 1.0001 + float(Q(cu - Fr(u0), cv - Fr(v0))) * 2, 10 ** 20)
tau = math.log(s0); tau1 = math.log(s1); n = 0; worst_mu = -9
cells = []
while tau < tau1:
    d_in = delta
    U, V = taylor(float(cu), float(cv), N)
    pu = [cu] + [rnd(x) for x in U[1:]]; pv = [cv] + [rnd(x) for x in V[1:]]
    du = padd(pder(pu), psc(-1, pmul(pu, padd(padd([Fr(3)], psc(-1, pu)), psc(-1, pv)))))
    dv = padd(pder(pv), psc(-1, pmul(pv, padd(pu, [Fr(-1)]))))
    eta = up(float(max(qabs(du, H), qabs(dv, H))) * 1.01 + 1e-30, 10 ** 30)
    rho = Fr(1, 1000)
    a0, a1 = lo(pu, H) - rho, hi(pu, H) + rho; b0, b1 = lo(pv, H) - rho, hi(pv, H) + rho
    # smallest mu on a grid of 1/1000 passing the four corners
    mu = Fr(-500, 1000)
    while not all(corner(mu, a, b) for a in (a0, a1) for b in (b0, b1)):
        mu += Fr(1, 1000)
        assert mu < 0, 'no contraction at tau=%g' % tau
    K = 2 * mu + kappa; assert K < 0
    C = 4 * eta * eta / kappa / (-K)
    assert delta < 2 * rho * rho and C < 2 * rho * rho
    B = delta / (1 - K * H) + C
    B = up(float(B) * 1.000001, 10 ** 24)
    worst_mu = max(worst_mu, float(mu))
    # next start: round the end value; link by Q_add_le
    eu, ev = peval(pu, H), peval(pv, H)
    cu, cv = rnd(float(eu)), rnd(float(ev))
    delta = up(float((1 + theta) * B + (1 + 1 / theta) * Q(cu - eu, cv - ev)) * 1.000001, 10 ** 24)
    cells.append((H, d_in, B, eta, mu, kappa, rho, a0, a1, b0, b1, pu, pv))
    tau += float(H); n += 1
    if n % 10 == 0 or tau >= tau1:
        print(f"cell {n:3d} s={math.exp(tau):9.1f} u={float(cu):.6f} v={float(cv):.6f} mu={float(mu):+.3f} "
              f"eta={float(eta):.1e} Q-bound={float(delta):.3e} (max-norm radius <= {math.sqrt(2*float(delta)):.2e})")
print(f"{n} cells, worst mu {worst_mu:+.3f}; start max-norm radius {r0:.2e}")

def q(x):
    x = Fr(x)
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"
def ql(l): return "[" + ", ".join(q(x) for x in l) + "]"
if len(sys.argv) > 5:
    out = sys.argv[5]
    L = ["import Work.Math.GContract", "",
         "/-! Gelfand problem, `GCData` (run 2026-11-20T1628Z): contracting homology cells in log radius from the end box",
         "of `GLamChain` onward, as data (generator `runs/2026-11-20T1628Z/scripts/gen_ccells.py`), decided as one chain by",
         "the kernel with the checks of `Work.Math.GContract.chainOK`. -/", "",
         "namespace Work.Math.GCData", "open Work.Math.GContract", ""]
    for k, c in enumerate(cells):
        L.append(f"def c{k} : CCell := ⟨{q(c[0])}, {q(c[1])}, {q(c[2])}, {q(c[3])}, {q(c[4])}, {q(c[5])}, {q(c[6])},")
        L.append(f"  {q(c[7])}, {q(c[8])}, {q(c[9])}, {q(c[10])},")
        L.append(f"  {ql(c[11])},")
        L.append(f"  {ql(c[12])}⟩")
        L.append("")
    L.append("def cells : List CCell := [" + ", ".join(f"c{k}" for k in range(len(cells))) + "]")
    L.append("")
    L.append("theorem chain_ok : chainOK cells = true := by decide +kernel")
    L.append("")
    L.append("end Work.Math.GCData")
    open(out, "w").write("\n".join(L) + "\n")
    print("wrote", out, len(cells), "cells; start", float(cells[0][11][0]), float(cells[0][12][0]), "delta0", float(cells[0][1]))
