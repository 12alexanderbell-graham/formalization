# Certificate generator for Work/Cosmography/B1Fit.lean (fit_direction).
# Exact rational arithmetic (fractions) for everything Lean will re-check; floats only to choose
# the certificate data. Lean checks every inequality; this script only proposes.
#
# Integrals J_k(Ω) = ∫_{w_k}^1 2/√(Ω+(1−Ω)v⁶) dv, w_k = 2^{-k/4}, k = 1, 3, 5.
# Lower bound on a cell [α,β] with c ≥ 0 (tangent of 1/√y):
#   (β−α)(3c − c³Ω) − c³(1−Ω)(β⁷−α⁷)/7
# Upper bound on a cell with p² ≤ y ≤ q² there (chord of 1/√y):
#   2(β−α)/p − 2/(pq(p+q)) · [ (β−α)Ω + (1−Ω)(β⁷−α⁷)/7 − (β−α)p² ]
from fractions import Fraction as F
import math, json, sys

KAPPA = F(95499, 100000)      # κ⁵⁰ < 1/10, so 10^(−1/50) > κ
assert KAPPA ** 50 < F(1, 10)
LLO = F(6931471803, 10**10)   # Real.log_two_gt_d9
LHI = F(6931471808, 10**10)   # Real.log_two_lt_d9
M = F(1044, 10000)            # > ℓ²/(2 ln 10) (checked in Lean)
assert LHI ** 2 / 2 / F(2302585092, 10**9) < M

def wexact(k): return 2 ** (-k / 4)

def rat(x, d=6, up=False):
    s = 10 ** d
    v = math.ceil(x * s) if up else math.floor(x * s)
    return F(v, s)

# rational bounds on w_k: lower-bound integrals start at wl ≥ w (shorter), upper at wu ≤ w
WL = {k: rat(wexact(k), 6, up=True) for k in (1, 3, 5)}
WU = {k: rat(wexact(k), 6, up=False) for k in (1, 3, 5)}
for k in (1, 3, 5):
    # w = (1+z)^{-1/2}, 1+z = 2^{k/2}; w ≤ wl ⇔ wl⁴·2^{k} ≥ 1 ; wu ≤ w ⇔ wu⁴ 2^k ≤ 1
    assert WL[k] ** 4 * 2 ** k >= 1 and WU[k] ** 4 * 2 ** k <= 1

def y(Om, v): return Om + (1 - Om) * v ** 6

def nodes(w0, N):
    h = (1 - w0) / N
    return [w0 + i * h for i in range(N + 1)]

def lower_cert(k, Ostar, N):
    w0 = WL[k]; vs = nodes(w0, N); cs = []
    A = F(0); B = F(0)
    for i in range(N):
        a_, b_ = vs[i], vs[i + 1]
        vm = float((a_ + b_) / 2)
        # choose c minimizing the cell error approx: c = y(vm)^{-1/2}, with 6 digits
        c = rat(y(Ostar, vm) ** -0.5, 6)
        cs.append(c)
        s7 = (b_ ** 7 - a_ ** 7) / 7
        # (β−α)(3c − c³Ω) − c³ s7 + c³ s7 Ω  = A_i − B_i Ω
        A += (b_ - a_) * 3 * c - c ** 3 * s7
        B += (b_ - a_) * c ** 3 - c ** 3 * s7
    return dict(k=k, Ostar=Ostar, N=N, w0=w0, cs=cs, A=A, B=B)

def upper_cert(k, Oa, Ob, N):
    w0 = WU[k]; vs = nodes(w0, N); ps = []; qs = []
    C = F(0); D = F(0)
    for i in range(N):
        a_, b_ = vs[i], vs[i + 1]
        ylo = y(Oa, a_); yhi = y(Ob, b_)
        p = rat(math.sqrt(float(ylo)), 6)
        while p * p > ylo: p -= F(1, 10 ** 6)
        q = rat(math.sqrt(float(yhi)), 6, up=True)
        while q * q < yhi: q += F(1, 10 ** 6)
        ps.append(p); qs.append(q)
        s7 = (b_ ** 7 - a_ ** 7) / 7
        g = 2 / (p * q * (p + q))
        # 2(β−α)/p − g[(β−α)Ω + s7 − s7Ω − (β−α)p²]
        C += 2 * (b_ - a_) / p - g * (s7 - (b_ - a_) * p * p)
        D += -g * ((b_ - a_) - s7)
    return dict(k=k, Oa=Oa, Ob=Ob, N=N, w0=w0, ps=ps, qs=qs, C=C, D=D)

def Lval(c, Om): return c['A'] - c['B'] * Om
def Uval(c, Om): return c['C'] + c['D'] * Om

# Q(u) = u + A2 u² + A3 u³, A2 = 3/2 − 3Ω/4, A3 = 9/8Ω² − 2Ω + 7/6 ; as poly in Ω: [c0,c1,c2]
def Qpoly(u):
    return [u + F(3, 2) * u ** 2 + F(7, 6) * u ** 3, -F(3, 4) * u ** 2 - 2 * u ** 3, F(9, 8) * u ** 3]
def Qlo(k): return Qpoly(k * LLO / 2)
def Qhi(k): return Qpoly(k * LHI / 2)
def padd(p, q, s=1): return [p[i] + s * q[i] for i in range(3)]
def pscale(p, s): return [s * x for x in p]
def peval(p, x): return p[0] + p[1] * x + p[2] * x * x

def pmin(p, a, b):
    vals = [peval(p, a), peval(p, b)]
    if p[2] > 0:
        xm = -p[1] / (2 * p[2])
        if a < xm < b: vals.append(peval(p, xm))
    return min(vals)

R = {(3, 1): F(2), (5, 3): F(2), (5, 1): F(4), (1, 3): F(1, 2), (3, 5): F(1, 2), (1, 5): F(1, 4)}

def try_case(a, b, pairs, low, upp):
    """pairs: list of (k, j): constraint P_k ≤ ρ P_j. Needs U_k, L_j.
    ρ = max over endpoints of r_kj U_k / (κ L_j), rounded up."""
    cons = []
    for (k, j) in pairs:
        r = R[(k, j)]
        Lc = low[j]; Uc = upp[k]
        rho = max(r * Uval(Uc, O) / (KAPPA * Lval(Lc, O)) for O in (a, b))
        rho = rat(float(rho), 6, up=True)
        while any(rho * KAPPA * Lval(Lc, O) < r * Uval(Uc, O) for O in (a, b)):
            rho += F(1, 10 ** 6)
        cons.append((k, j, rho))
    # solve λ: c2 = Σλ(ρ j² − k²)/4 = −1, c3 = Σλ(ρ j³ − k³)/8 = 20/3
    # then (20/3)e3 − e2 ≥ Σ λ (Q_k − ρ Q_j)
    (k1, j1, r1), (k2, j2, r2) = cons
    a11 = (r1 * j1 ** 2 - k1 ** 2) / 4; a12 = (r2 * j2 ** 2 - k2 ** 2) / 4
    a21 = (r1 * j1 ** 3 - k1 ** 3) / 8; a22 = (r2 * j2 ** 3 - k2 ** 3) / 8
    det = a11 * a22 - a12 * a21
    if det == 0: return None
    l1 = (-1 * a22 - a12 * F(20, 3)) / det
    l2 = (a11 * F(20, 3) - a21 * -1) / det
    if l1 < 0 or l2 < 0: return None
    # S(Ω) = Σ λ (Q_k − ρ Q_j) with Q_k ≥ Qlo_k, Q_j ≤ Qhi_j  (ρ, λ ≥ 0)
    S = [F(0)] * 3
    for (k, j, rho), lam in zip(cons, (l1, l2)):
        S = padd(S, pscale(padd(Qlo(k), pscale(Qhi(j), rho), -1), lam))
    mn = pmin(S, a, b)
    return dict(a=a, b=b, cons=cons, lam=(l1, l2), S=S, min=mn, ok=mn > M)

if __name__ == '__main__':
    import itertools
    NL = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    # quick accuracy test of cells
    import mpmath as mp
    def Jtrue(k, Om, w0):
        return mp.quad(lambda v: 2 / mp.sqrt(Om + (1 - Om) * v ** 6), [float(w0), 1])
    for k in (1, 3, 5):
        for Om in (F(0), F(3, 10), F(1)):
            lc = lower_cert(k, Om, NL)
            uc = upper_cert(k, Om, Om, NL)
            jt = Jtrue(k, float(Om), wexact(k))
            print(k, float(Om), 'lowrel', float((jt - float(Lval(lc, Om))) / jt), 'uprel', float((float(Uval(uc, Om)) - jt) / jt))

# ---------------- Lean emission ----------------
def fstr(x):
    x = F(x)
    if x.denominator == 1: return f"({x.numerator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"

def lower_trunc(c, digits=9):
    s = 10 ** digits
    A_ = F(math.floor(c['A'] * s), s); B_ = F(math.ceil(c['B'] * s), s)
    return A_, B_

def emit_lower(name, c):
    A_, B_ = lower_trunc(c)
    c['A_'], c['B_'] = A_, B_
    N = c['N']; w0 = c['w0']; h = (1 - w0) / N
    lst = ", ".join(str(int(x * 10 ** 6)) for x in c['cs'])
    return f"""def c{name} : List ℕ := [{lst}]

lemma {name} (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    {fstr(A_)} - {fstr(B_)} * Ω ≤ ∫ v in {fstr(w0)}..1, gL Ω v := by
  have key := sum_lower Ω h0 h1 {fstr(w0)} {fstr(h)} (by norm_num) (by norm_num)
    (fun i => (c{name}.getD i 0 : ℝ) / 1000000) (fun i => by positivity) {N}
  have e : {fstr(w0)} + (({N}:ℕ):ℝ) * {fstr(h)} = 1 := by norm_num
  rw [e] at key
  refine le_trans ?_ key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c{name}]
  norm_num
  linarith
"""

def upper_round(c, digits=9):
    s = 10 ** digits
    return F(math.ceil(c['C'] * s), s), F(math.ceil(c['D'] * s), s)

def emit_upper(name, c):
    C_, D_ = upper_round(c)
    c['C_'], c['D_'] = C_, D_
    N = c['N']; w0 = c['w0']; h = (1 - w0) / N
    pl = ", ".join(str(int(x * 10 ** 6)) for x in c['ps'])
    ql = ", ".join(str(int(x * 10 ** 6)) for x in c['qs'])
    Oa, Ob = c['Oa'], c['Ob']
    return f"""def p{name} : List ℕ := [{pl}]
def q{name} : List ℕ := [{ql}]

lemma {name} (Ω : ℝ) (ha : {fstr(Oa)} ≤ Ω) (hb : Ω ≤ {fstr(Ob)}) :
    ∫ v in {fstr(w0)}..1, gL Ω v ≤ {fstr(C_)} + {fstr(D_)} * Ω := by
  have key := sum_upper Ω (by linarith) (by linarith) {fstr(w0)} {fstr(h)} (by norm_num) (by norm_num)
    (fun i => (p{name}.getD i 0 : ℝ) / 1000000) (fun i => (q{name}.getD i 0 : ℝ) / 1000000) {N}
    (fun i hi => by interval_cases i <;> norm_num [p{name}])
    (fun i hi => by interval_cases i <;> norm_num [q{name}])
    (fun i hi => by interval_cases i <;> norm_num [p{name}] <;> linarith)
    (fun i hi => by interval_cases i <;> norm_num [q{name}] <;> linarith)
  have e : {fstr(w0)} + (({N}:ℕ):ℝ) * {fstr(h)} = 1 := by norm_num
  rw [e] at key
  refine le_trans key ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p{name}, q{name}]
  norm_num
  linarith
"""
