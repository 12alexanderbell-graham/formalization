"""Independent sympy derivation of the cosmography formulas in Sec. 10 of
Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421 (Eqs. 10.1-10.68),
compared against transcriptions of the typeset equations (read from page images).

Conventions (paper's, Eqs. 10.1-10.5): H = a'/a, q = -a''/(aH^2), j = +a'''/(aH^3),
s = +a''''/(aH^4), l = +a'''''/(aH^5).  1+z = a0/a.  D = c(t0 - t*).
Dimensionless: x = H0 D / c, Ok = K c^2/(H0^2 a0^2) (K = +1 closed -> sin).
Units c = H0 = a0 = 1 in the series.
"""
import sympy as sp

q, j, s, l, Ok, Om0 = sp.symbols('q0 j0 s0 l0 Ok Omega0')
x, z, y, tau = sp.symbols('x z y tau')
N = 6  # keep through x^5


def trunc(e, v, n=N):
    e = sp.expand(e)
    return sum(e.coeff(v, k)*v**k for k in range(n))
def compose(e, v, inner, w, n=N):
    """e(v) polynomial, substitute v=inner(w) (inner has no constant term), truncate at w^n"""
    e = sp.expand(e); res = 0; p = sp.Integer(1)
    for k in range(n):
        res += e.coeff(v, k)*p
        p = trunc(p*inner, w, n)
    return trunc(res, w, n)

results = []
def cmp(eq, name, printed, correct):
    d = sp.expand(printed - correct)
    results.append((eq, name, sp.simplify(d) == 0, d))
    print(f"{eq:10s} {name:12s} {'OK ' if d == 0 else 'MISMATCH'}  printed-correct = {d}")

# ---------- (10.6)-(10.9): derivatives of H ----------
t = sp.symbols('t')
a = sp.Function('a')(t)
H = a.diff(t)/a
Hs = sp.Symbol('H')
# a^(n) = a * H^n * {1, -q, j, s, l}
sub = {a.diff(t, 5): a*Hs**5*l, a.diff(t, 4): a*Hs**4*s,
       a.diff(t, 3): a*Hs**3*j, a.diff(t, 2): -a*Hs**2*q, a.diff(t): a*Hs}
def red(e):
    return sp.simplify(sp.expand(e.subs(sub)))
cmp('(10.6)', 'Hdot', -Hs**2*(1+q), red(H.diff(t)))
cmp('(10.7)', 'Hddot', Hs**3*(j+3*q+2), red(H.diff(t, 2)))
cmp('(10.8)', 'H3dot', Hs**4*(s-4*j-3*q*(q+4)-6), red(H.diff(t, 3)))
cmp('(10.9)', 'H4dot', Hs**5*(l-5*s+10*(q+2)*j+30*(q+2)*q+24), red(H.diff(t, 4)))

# ---------- (10.10)-(10.12): a(t) series ----------
a_tau = 1 + tau - q/2*tau**2 + j/6*tau**3 + s/24*tau**4 + l/120*tau**5  # a/a0, tau = H0(t-t0)
a_emit = a_tau.subs(tau, -x)  # a(t0 - D/c)/a0
cmp('(10.12)', 'denominator', 1 - x - q/2*x**2 - j/6*x**3 + s/24*x**4 - l/120*x**5, sp.expand(a_emit))

# ---------- (10.13)-(10.19): 1+z as series in x ----------
onepz = sp.series(1/a_emit, x, 0, N).removeO()
Zc = [sp.expand(onepz.coeff(x, k)) for k in range(N)]
Zp = {1: 1, 2: 1+q/2, 3: 1+q+j/6, 4: 1+sp.Rational(3, 2)*q+q**2/4+j/3-s/24,
      5: 1+2*q+sp.Rational(3, 4)*q**2+q*j/6+j/2-s/12+l}
for k in range(1, 6):
    cmp('(10.%d)' % (14+k), 'Z_D^%d' % k, Zp[k], Zc[k])
print('  (10.13) uses identical coefficients to (10.15)-(10.19); x^5 coeff correct =', Zc[5])

# ---------- (10.20)-(10.25): D(z) ----------
zx = sum(Zc[k]*x**k for k in range(1, N))
# invert z(x) -> x(z)
cs = sp.symbols('c1:7')
xz = sum(cs[k-1]*z**k for k in range(1, N))
eqs = sp.expand(sp.series(zx.subs(x, xz), z, 0, N).removeO()) - z
sol = sp.solve([eqs.coeff(z, k) for k in range(1, N)], cs[:N-1], dict=True)[0]
xz = sp.expand(xz.subs(sol))
Dc = [sp.expand(xz.coeff(z, k+1)) for k in range(5)]
Dp = [1, -(1+q/2), 1+q+q**2/2-j/6,
      -(1+sp.Rational(3, 2)*q+sp.Rational(3, 2)*q**2+sp.Rational(5, 8)*q**3-j/2-sp.Rational(5, 12)*q*j-s/24),
      1+2*q+3*q**2+sp.Rational(5, 2)*q**3+sp.Rational(7, 2)*q**4-sp.Rational(5, 3)*q*j-sp.Rational(7, 8)*q**2*j
      - q*s/8 - j + j**2/12 - s/6 - l/120]
for k in range(5):
    cmp('(10.%d)' % (21+k), 'D_z^%d' % k, Dp[k], Dc[k])
print('  correct D_z^4 =', Dc[4])
# also: what D_z^4 would be if derived from the printed (wrong-l) Z_D^5
zx_pr = sum(Zp[k]*x**k for k in range(1, 6))
xz2 = sum(cs[k-1]*z**k for k in range(1, N))
eqs2 = sp.expand(sp.series(zx_pr.subs(x, xz2), z, 0, N).removeO()) - z
sol2 = sp.solve([eqs2.coeff(z, k) for k in range(1, N)], cs[:N-1], dict=True)[0]
print('  D_z^4 from printed Z_D^5 (diagnostic) =', sp.expand(cs[4].subs(sol2)))

# ---------- (10.29): flat r0 ----------
X = sp.integrate(sp.series(1/a_tau.subs(tau, -sp.Symbol('u')), sp.Symbol('u'), 0, N).removeO(),
                 (sp.Symbol('u'), 0, x))  # H0 a0 chi / c  (chi = int c dt / a)
X = sp.expand(X)
Rflat = [sp.expand(X.coeff(x, k+1)) for k in range(6)]
Pflat = [1, sp.Rational(1, 2), (2+q)/6, (6+6*q+j)/24, (24+36*q+6*q**2+8*j-s)/120,
         (12+24*q+9*q**2+2*q*j+6*j-s+12*l)/72]
for k in range(6):
    cmp('(10.29)', 'flat x^%d' % k, Pflat[k], Rflat[k])

# ---------- (10.31)-(10.37): curved r0 ----------
S = sp.expand(X - Ok*X**3/6 + Ok**2*X**5/120)  # a0 r0 H0/c, through x^5 (X^7 is O(x^7))
S = sum(S.coeff(x, k)*x**k for k in range(N+1))
Rc = [sp.expand(S.coeff(x, k+1)) for k in range(6)]
Rp = [1, sp.Rational(1, 2), (2+q-Ok)/6, (6+6*q+j-6*Ok)/24,
      (24+36*q+6*q**2+8*j-s-5*Ok*(7+2*q))/120,
      (24+48*q+18*q**2+4*q*j+12*j-2*s+24*l-3*Ok*(15+10*q+j))/144]
for k in range(6):
    cmp('(10.%d)' % (32+k), 'R_D^%d' % k, Rp[k], Rc[k])

# ---------- (10.38)-(10.51): d_L, d_A in z ----------
dL_x = trunc(S*onepz, x, N+1)        # d_L H0/c as series in x
dA_x = trunc(S*trunc(sp.series(a_emit, x, 0, N+1).removeO(), x, N+1), x, N+1)
def zser(e):
    e = compose(trunc(e, x), x, xz, z)
    return [sp.expand(e.coeff(z, k+1)) for k in range(5)]
DLc = zser(dL_x)
DAc = zser(dA_x)
DLp = [1, -(-1+q)/2, -(1-q-3*q**2+j+Ok)/6,
       (2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*Ok*(1+3*q))/24,
       (-6+6*q+81*q**2+165*q**3+105*q**4-110*q*j-105*q**2*j-15*q*s
        - 27*j+10*j**2-11*s-l-5*Ok*(1+8*q+9*q**2-2*j))/120]
DAp = [1, -(3+q)/2, (11+7*q+3*q**2-j-Ok)/6,
       -(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s-2*Ok*(5+3*q))/24,
       (274+326*q+411*q**2+315*q**3+105*q**4-210*q*j-105*q**2*j-15*q*s
        - 137*j+10*j**2-21*s-l-5*Ok*(17+20*q+9*q**2-2*j))/120]
for k in range(5):
    cmp('(10.%d)' % (39+k), 'D_L^%d' % k, DLp[k], DLc[k])
for k in range(5):
    cmp('(10.%d)' % (46+k), 'D_A^%d' % k, DAp[k], DAc[k])

# ---------- (10.52)-(10.63): y = z/(1+z), Omega0 = 1 + Ok ----------
def yser(e):
    zy = sum(y**k for k in range(1, N+1))
    xy = compose(xz, z, zy, y)
    e = compose(trunc(e, x), x, xy, y)
    return [sp.expand(e.coeff(y, k+1).subs(Ok, Om0-1)) for k in range(5)]
DLyc = yser(dL_x)
DAyc = yser(dA_x)
O = Om0
DLyp = [1, -(-3+q)/2, -(12-5*q+3*q**2-j-O)/6,
        (52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*O*(1+3*q))/24,
        (359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s
         - 57*j+10*j**2+9*s-l-5*O*(17-6*q+9*q**2-2*j))/120]
DAyp = [1, -(1+q)/2, -(-q-3*q**2+j+O)/6,
        -(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*O)/24,
        -(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s
          - 3*j-10*j**2+s+l+5*O)/120]
for k in range(5):
    cmp('(10.%d)' % (52+k), 'D_Ly^%d' % k, DLyp[k], DLyc[k])
for k in range(5):
    cmp('(10.%d)' % (58+k), 'D_Ay^%d' % k, DAyp[k], DAyc[k])

# ---------- (10.64)-(10.68): mu(z), flat ----------
flatL = sum(DLc[k].subs(Ok, 0)*z**k for k in range(5))
lg = sp.expand(sp.series(sp.log(flatL), z, 0, 5).removeO())
Mc = [sp.expand(lg.coeff(z, k)) for k in range(1, 5)]
Mp = [-(-1+q)/2, -(7-10*q-9*q**2+4*j)/24, (5-9*q-16*q**2-10*q**3+7*j+8*q*j+s)/24,
      (-469+1004*q+2654*q**2+3300*q**3+1575*q**4+200*j**2-1148*j
       - 2620*q*j-1800*q**2*j-300*q*s-324*s-24*l)/2880]
for k in range(4):
    cmp('(10.%d)' % (65+k), 'M^%d' % (k+1), Mp[k], Mc[k])

print('\n==== correct expressions ====')
for nm, lst in [('Z_D', Zc[1:]), ('D_z', Dc), ('R_D', Rc), ('D_L', DLc), ('D_A', DAc),
                ('D_Ly', DLyc), ('D_Ay', DAyc), ('M', Mc)]:
    for k, e in enumerate(lst):
        print(nm, k, sp.factor_terms(e) if nm != 'M' else e)
