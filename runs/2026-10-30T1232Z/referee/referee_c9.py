"""Referee check for C9 (Bamba et al. 2012, Eqs. (10.38)-(10.51)).

Route (independent of the repository's y-series transfer):
 (A) generic scale factor: a(tau) = 1 + tau - q tau^2/2 + j tau^3/6 + s tau^4/24 + l tau^5/120 + m tau^6/720
     (H0 = a0 = 1, so k = K), invert 1+z = 1/a(tau) for tau(z) directly, integrate chi = int_tau^0 dt/a,
     d_L = (1+z) S_K(chi) with the FULL sin/sinh series, d_A = d_L/(1+z)^2, read off z^5 coefficients.
 (B) exact closed-form models, Taylor expanded directly in z from closed forms:
     Milne a = t (K=-1), closed de Sitter a = cosh t (K=+1), open de Sitter a = sinh t (K=-1),
     a = e^t with K = +-1, open/closed dust (Mattig), where q,j,s,l are computed from H(z).
Compares to the printed D^n_L, D^n_A.
"""
import sympy as sp, time

z, tau, x = sp.symbols('z tau x')
q, j, s, l, m, k = sp.symbols('q j s l m k')
N = 6  # order in z of H0 d_L (z^1..z^5 needed)


def DL_printed(q, j, s, l, k):
    return [sp.Integer(1), -sp.Rational(1, 2)*(-1 + q),
            -sp.Rational(1, 6)*(1 - q - 3*q**2 + j + k),
            sp.Rational(1, 24)*(2 - 2*q - 15*q**2 - 15*q**3 + 5*j + 10*q*j + s + 2*k*(1 + 3*q)),
            sp.Rational(1, 120)*(-6 + 6*q + 81*q**2 + 165*q**3 + 105*q**4 - 110*q*j - 105*q**2*j
                                 - 15*q*s - 27*j + 10*j**2 - 11*s - l - 5*k*(1 + 8*q + 9*q**2 - 2*j))]


def DA_printed(q, j, s, l, k):
    return [sp.Integer(1), -sp.Rational(1, 2)*(3 + q),
            sp.Rational(1, 6)*(11 + 7*q + 3*q**2 - j - k),
            -sp.Rational(1, 24)*(50 + 46*q + 39*q**2 + 15*q**3 - 13*j - 10*q*j - s - 2*k*(5 + 3*q)),
            sp.Rational(1, 120)*(274 + 326*q + 411*q**2 + 315*q**3 + 105*q**4 - 210*q*j - 105*q**2*j
                                 - 15*q*s - 137*j + 10*j**2 - 21*s - l - 5*k*(17 + 20*q + 9*q**2 - 2*j))]


def SK(K, chi, order=9):
    # full series of sin(sqrt K chi)/sqrt K, valid for every sign of K
    return sum((-K)**n * chi**(2*n+1) / sp.factorial(2*n+1) for n in range(order))


# ---------- (A) generic ----------
def mul(A,B):
    C=[0]*(N+1)
    for i,x in enumerate(A):
        if x==0: continue
        for jj,y in enumerate(B):
            if i+jj<=N and y!=0: C[i+jj]=sp.expand(C[i+jj]+x*y)
    return C
def add(*As):
    return [sp.expand(sum(c)) for c in zip(*As)]
def scal(c,A): return [sp.expand(c*x) for x in A]
def powr(A,n):
    R=[1]+[0]*N
    for _ in range(n): R=mul(R,A)
    return R
def compose(P,T):  # P(T), T[0]=0
    R=[0]*(N+1); Tp=[1]+[0]*N
    for i,c in enumerate(P):
        if i>0: Tp=mul(Tp,T)
        R=add(R,scal(c,Tp))
    return R
t0=time.time()
a=[1,1,-q/2,j/6,s/24,l/120,m/720]
u=a[:]; u[0]=0
inva=[1]+[0]*N
term=[1]+[0]*N
for n in range(1,N+1):
    term=scal(-1,mul(term,u)); inva=add(inva,term)
P=inva[:]; P[0]=0  # z = P(tau)
# reversion: tau = T(z)
T=[0,sp.Integer(1)/P[1]]+[0]*(N-1)
for n in range(2,N+1):
    c=sp.Symbol('c'); Tt=T[:]; Tt[n]=c
    e=compose(P,Tt)[n]
    T[n]=sp.expand(sp.solve(e,c)[0])
F=[0]+[sp.expand(inva[i-1]/i) for i in range(1,N+1)]
chi=scal(-1,compose(F,T))
chi3=powr(chi,3); chi5=powr(chi,5)
S=add(chi,scal(-k/6,chi3),scal(k**2/120,chi5))
dL=mul([1,1]+[0]*(N-1),S)
dA=mul([(-1)**i for i in range(N+1)],S)

print("(A) generic C^6 scale factor, H0 = a0 = 1, k = K (truncated-series reversion, no y-series):", flush=True)
for name, d, P in (("D_L", dL, DL_printed(q, j, s, l, k)), ("D_A", dA, DA_printed(q, j, s, l, k))):
    for n in range(5):
        print(f"  {name}^{n}: true - printed = {sp.factor(sp.expand(d[n+1] - P[n]))}", flush=True)

# ---------- (B) exact models ----------
print("\n(B) exact models (series of the closed form vs printed with model q,j,s,l,k):")


def params_from_a(aexpr, t, t0):
    a0 = aexpr.subs(t, t0)
    H0 = (sp.diff(aexpr, t)/aexpr).subs(t, t0)
    c = [sp.simplify((sp.diff(aexpr, t, n)/(aexpr*H0**n)).subs(t, t0)) for n in range(6)]
    return sp.simplify(a0), sp.simplify(H0), -c[2], c[3], c[4], c[5]


def check(label, H0dL_closed, qv, jv, sv, lv, kv):
    ser = sp.expand(sp.series(H0dL_closed, z, 0, 6).removeO())
    inv2 = sum((n+1)*(-z)**n for n in range(6))
    serA = sp.expand(ser*inv2)
    PL = DL_printed(qv, jv, sv, lv, kv)
    PA = DA_printed(qv, jv, sv, lv, kv)
    out = []
    for n in range(5):
        dl = sp.nsimplify(sp.N(ser.coeff(z, n+1) - PL[n], 50), rational=True, tolerance=1e-30)
        da = sp.nsimplify(sp.N(serA.coeff(z, n+1) - PA[n], 50), rational=True, tolerance=1e-30)
        out.append((dl, da))
    print(f"  {label}: q={qv}, j={jv}, s={sv}, l={lv}, k={kv}, k^2/120={sp.nsimplify(sp.N(kv**2/120, 50), rational=True, tolerance=1e-30)}")
    print("     true-printed (L,A) for D^0..D^4:", out)


t = sp.symbols('t', positive=True)
zp = sp.symbols('zp')
# Milne: a = t, t0 = 1, K = -1: 1+z = 1/t, chi = ln(1+z), d_L = (1+z) sinh(chi) = z + z^2/2
check("Milne a=t, K=-1", sp.expand((1+z)*sp.sinh(sp.log(1+z)).rewrite(sp.exp)), 0, 0, 0, 0, sp.Integer(-1))
# exact models via chi(z) = int_0^z dz'/(a0 H(z')), H as closed function of a = a0/(1+z)
models = ((sp.cosh(t), 1, sp.acosh(2), lambda A: sp.sqrt(1 - 1/A**2), "closed dS a=cosh t, K=+1, a0=2"),
          (sp.sinh(t), -1, sp.asinh(sp.Rational(3, 4)), lambda A: sp.sqrt(1 + 1/A**2), "open dS a=sinh t, K=-1, a0=3/4"),
          (sp.exp(t), 1, sp.Integer(0), lambda A: sp.Integer(1), "a=e^t, K=+1"),
          (sp.exp(t), -1, sp.Integer(0), lambda A: sp.Integer(1), "a=e^t, K=-1"))
for (aexpr, K, t0_, Hfun, lab) in models:
    a0_, H0_, qv, jv, sv, lv = params_from_a(aexpr, t, t0_)
    kv = sp.simplify(K/(H0_**2*a0_**2))
    integrand = sp.series(1/(a0_*Hfun(a0_/(1+zp))), zp, 0, 6).removeO()
    chi_ = sp.integrate(integrand, (zp, 0, z))
    SKc = sum((-K)**n*chi_**(2*n+1)/sp.factorial(2*n+1) for n in range(4))
    check(lab, sp.expand(H0_*a0_*(1+z)*SKc), qv, jv, sv, lv, kv)

# dust (Lambda = 0), Mattig: H0 d_L = (2/Om^2)[Om z + (Om - 2)(sqrt(1+Om z) - 1)], k = Om - 1
# q,j,s,l from H(z): H^2 = Om(1+z)^3 + (1-Om)(1+z)^2, d/dt = -(1+z) H d/dz, a = 1/(1+z)
for Om in (sp.Rational(3, 10), sp.Rational(2), sp.Rational(1, 2)):
    Hz = sp.sqrt(Om*(1+z)**3 + (1-Om)*(1+z)**2)
    f = 1/(1+z)
    ders = [f]
    for n in range(5):
        ders.append(sp.simplify(-(1+z)*Hz*sp.diff(ders[-1], z)))
    c = [sp.simplify((ders[n]/(f*Hz**n)).subs(z, 0)) for n in range(6)]
    mattig = 2/Om**2*(Om*z + (Om - 2)*(sp.sqrt(1 + Om*z) - 1))
    check(f"dust Mattig Om={Om}", mattig, -c[2], c[3], c[4], c[5], Om - 1)

# ---------- size of the omitted term ----------
print("\n(C) size of the omitted term: |Delta(H0 d_L)| = k^2 z^5/120, relative to H0 d_L ~ z:")
for Ok in (0.001, 0.01, 0.1, 0.3, 1.0):
    row = []
    for zz in (0.5, 1.0, 1.5, 2.0):
        row.append(f"z={zz}: {Ok**2*zz**4/120:.1e}")
    print(f"  |Omega_k|={Ok}: rel. shift k^2 z^4/120 ->", ", ".join(row))
