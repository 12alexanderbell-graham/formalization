"""Contracting homology cells in log radius from the end box of GLamChain (s = 8579/20) through the fourth and
fifth turning points of the radial Gelfand branch, in segments with per-cell predicates (run 2026-11-21T0428Z).
Every condition is checked here in exact rationals with the definitions of Work.Math.GContract (CCProp, LinkProp)
and Work.Math.GSeg (inB, vLtB, vGtB, uInB); the kernel re-decides them in Lean.
Segments (offsets x from tau0 = log(8579/20)):  A [0, X3a] none;  P3 [.., X3a] v > 2;  C3 [X3a, X3b] u in [L3, U3]
with U3 <= 1;  B [X3b, X4a] v < 2;  C4 [X4a, X4b] u in [L4, U4] with L4 >= 1;  D [X4b, X4b + hD] v > 2.
Usage: python3 gen_seg.py [out.lean]"""
import sys, math
from fractions import Fraction as Fr
import numpy as np
from scipy.integrate import solve_ivp

N = 14; DEN = 10 ** 16
CU = Fr(131783194069, 125000000000); CV = Fr(1000004740803, 500000000000); R0 = Fr(649, 125000000)
s0 = 8579 / 20
def f(s, y):
    w, p = y; return [p, -2 / s * p - math.exp(w)]
z = 1e-3
sol = solve_ivp(f, [z, 60000], [-z * z / 6, -z / 3], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True)
def uv_at(x):  # float u, v at offset x
    s = s0 * math.exp(x); w, p = sol.sol(s); return s * math.exp(w) / (-p), -s * p

def rnd(x): return Fr(round(x * DEN), DEN)
def taylor(u, v, n):
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
def up(x, d=10 ** 12): return Fr(math.ceil(x * d), d)
theta = Fr(1, 1000); kappa = Fr(1, 100); rho = Fr(1, 1000)

def make_cell(cu, cv, delta, H):
    U, V = taylor(float(cu), float(cv), N)
    pu = [cu] + [rnd(x) for x in U[1:]]; pv = [cv] + [rnd(x) for x in V[1:]]
    du = padd(pder(pu), psc(-1, pmul(pu, padd(padd([Fr(3)], psc(-1, pu)), psc(-1, pv)))))
    dv = padd(pder(pv), psc(-1, pmul(pv, padd(pu, [Fr(-1)]))))
    eta = up(float(max(qabs(du, H), qabs(dv, H))) * 1.01 + 1e-30, 10 ** 30)
    a0, a1 = lo(pu, H) - rho, hi(pu, H) + rho; b0, b1 = lo(pv, H) - rho, hi(pv, H) + rho
    mu = Fr(-500, 1000)
    while not all(corner(mu, a, b) for a in (a0, a1) for b in (b0, b1)):
        mu += Fr(1, 1000); assert mu < 0
    K = 2 * mu + kappa; assert K < 0
    C = 4 * eta * eta / kappa / (-K)
    assert delta < 2 * rho * rho and C < 2 * rho * rho
    B = up(float(delta / (1 - K * H) + C) * 1.000001, 10 ** 24)
    assert delta / (1 - K * H) + C <= B
    return dict(h=H, d=delta, B=B, eta=eta, mu=mu, kappa=kappa, rho=rho, a0=a0, a1=a1, b0=b0, b1=b1, pu=pu, pv=pv)
def inB(c): return c['d'] + 4 * c['eta'] ** 2 / c['kappa'] / (-(2 * c['mu'] + c['kappa']))
def vLt(y, c): h = hi(c['pv'], c['h']); return h < y and 2 * inB(c) < (y - h) ** 2
def vGt(y, c): l = lo(c['pv'], c['h']); return y < l and 2 * inB(c) < (l - y) ** 2
def uIn(L, U_, c):
    l = lo(c['pu'], c['h']); h = hi(c['pu'], c['h'])
    return L < l and 2 * inB(c) < (l - L) ** 2 and h < U_ and 2 * inB(c) < (U_ - h) ** 2
def link(c):  # next start values and delta
    eu, ev = peval(c['pu'], c['h']), peval(c['pv'], c['h'])
    nu, nv = rnd(float(eu)), rnd(float(ev))
    nd = up(float((1 + theta) * c['B'] + (1 + 1 / theta) * Q(nu - eu, nv - ev)) * 1.000001, 10 ** 24)
    assert (1 + theta) * c['B'] + (1 + 1 / theta) * Q(nu - eu, nv - ev) <= nd
    return nu, nv, nd

state = {'cu': CU, 'cv': CV, 'd': up(float(Fr(7, 2) * R0 * R0) * 1.000001, 10 ** 24), 'x': Fr(0)}
assert Fr(7, 2) * R0 * R0 <= state['d']
def segment(xend, pred, hmax=Fr(1, 10)):
    cells = []
    while state['x'] < xend:
        H = min(hmax, xend - state['x'])
        while True:
            c = make_cell(state['cu'], state['cv'], state['d'], H)
            if pred is None or pred(c): break
            H = H / 2
            assert H > Fr(1, 10 ** 6), 'predicate fails at x=%s' % float(state['x'])
        cells.append(c)
        state['x'] += H
        state['cu'], state['cv'], state['d'] = link(c)
    return cells

# breakpoints (offsets): crossings of v = 2 from the float solution
def zero_v(xa, xb):
    for _ in range(80):
        xm = (xa + xb) / 2
        if (uv_at(xa)[1] - 2) * (uv_at(xm)[1] - 2) <= 0: xb = xm
        else: xa = xm
    return xa
tau0 = math.log(s0)
x3 = zero_v(8.40 - tau0, 8.44 - tau0); x4 = zero_v(10.78 - tau0, 10.82 - tau0)
print("x3 =", x3, "s3 =", s0 * math.exp(x3), "lam3 =", np.prod(uv_at(x3)))
print("x4 =", x4, "s4 =", s0 * math.exp(x4), "lam4 =", np.prod(uv_at(x4)))
W3 = Fr(1, 2500); W4 = Fr(1, 500)
X3a = Fr(round(x3 * 10000), 10000) - W3; X3b = X3a + 2 * W3
X4a = Fr(round(x4 * 10000), 10000) - W4; X4b = X4a + 2 * W4
assert X3a < x3 < X3b and X4a < x4 < X4b
u3 = [uv_at(float(X3a))[0], uv_at(float(X3b))[0]]; u4 = [uv_at(float(X4a))[0], uv_at(float(X4b))[0]]
SL = 1.5e-5
L3 = Fr(math.floor((min(u3) - SL) * 1e6), 10 ** 6); U3 = Fr(math.ceil((max(u3) + SL) * 1e6), 10 ** 6)
L4 = Fr(math.floor((min(u4) - SL) * 1e6), 10 ** 6); U4 = Fr(math.ceil((max(u4) + SL) * 1e6), 10 ** 6)
print("u3 enclosure", float(L3), float(U3), "u4 enclosure", float(L4), float(U4))
assert U3 <= 1 and L4 >= 1
XP3 = X3a - Fr(1, 100)
segA = segment(XP3, None)
segP = segment(X3a, lambda c: vGt(2, c))
segC3 = segment(X3b, lambda c: uIn(L3, U3, c))
segB = segment(X4a, lambda c: vLt(2, c))
segC4 = segment(X4b, lambda c: uIn(L4, U4, c))
segD = segment(X4b + Fr(1, 1000), lambda c: vGt(2, c))
segs = [('A', segA, None), ('P', segP, 'vGtB 2'), ('C3', segC3, f'uInB L3 U3'), ('B', segB, 'vLtB 2'),
        ('C4', segC4, 'uInB L4 U4'), ('D', segD, 'vGtB 2')]
for nm, cs, _ in segs:
    print(nm, len(cs), "cells, length", float(sum(c['h'] for c in cs)), "end delta", float(cs[-1]['B']))
print("X3a X3b X4a X4b", X3a, X3b, X4a, X4b)

def q(x):
    x = Fr(x); return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"
def ql(l): return "[" + ", ".join(q(x) for x in l) + "]"
if len(sys.argv) > 1:
    L = ["import Work.Math.GSeg", "",
         "/-! Gelfand problem, `GSegData` (run 2026-11-21T0428Z): contracting homology cells in log radius from the end box",
         "of `GLamChain` (radius 8579/20) through the fourth and fifth turning points, in six segments, as data (generator",
         "`runs/2026-11-21T0428Z/scripts/gen_seg.py`); each segment is decided by the kernel as one chain with its cell",
         "predicate, and consecutive segments are linked. -/", "",
         "namespace Work.Math.GSegData", "open Work.Math.GContract Work.Math.GSeg", "",
         f"def L3 : ℚ := {q(L3)}", f"def U3 : ℚ := {q(U3)}", f"def L4 : ℚ := {q(L4)}", f"def U4 : ℚ := {q(U4)}", ""]
    for nm, cs, _ in segs:
        for k, c in enumerate(cs):
            L.append(f"def {nm.lower()}{k} : CCell := ⟨{q(c['h'])}, {q(c['d'])}, {q(c['B'])}, {q(c['eta'])}, {q(c['mu'])}, {q(c['kappa'])}, {q(c['rho'])},")
            L.append(f"  {q(c['a0'])}, {q(c['a1'])}, {q(c['b0'])}, {q(c['b1'])},")
            L.append(f"  {ql(c['pu'])},")
            L.append(f"  {ql(c['pv'])}⟩")
            L.append("")
        L.append(f"def seg{nm} : List CCell := [" + ", ".join(f"{nm.lower()}{k}" for k in range(len(cs))) + "]")
        L.append("")
    for nm, cs, pr in segs:
        L.append(f"theorem seg{nm}_ok : chainOK seg{nm} = true := by decide +kernel")
        if pr: L.append(f"theorem seg{nm}_pred : seg{nm}.all ({pr}) = true := by decide +kernel")
        L.append(f"theorem seg{nm}_len : totalH seg{nm} = {q(sum(c['h'] for c in cs))} := by decide +kernel")
    for (a, ca, _), (b, cb, _) in zip(segs, segs[1:]):
        L.append(f"theorem link{a}{b} : decide (LinkProp {a.lower()}{len(ca)-1} {b.lower()}0) = true := by decide +kernel")
    L.append(f"theorem start_ok : (a0.pu.headD 0 = {q(CU)}) ∧ a0.pv.headD 0 = {q(CV)} ∧ (7 / 2 : ℚ) * {q(R0)} ^ 2 ≤ a0.δ := by decide +kernel")
    L += ["", "end Work.Math.GSegData"]
    open(sys.argv[1], "w").write("\n".join(L) + "\n")
    print("wrote", sys.argv[1])
