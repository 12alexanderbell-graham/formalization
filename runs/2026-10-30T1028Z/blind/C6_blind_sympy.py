"""Blind derivation of the y-series of the luminosity distance, general curvature K.

Conventions (Bamba et al. 2012, Sec. X): H = a'/a, q = -a''/(a H^2), j = a'''/(a H^3),
s = a''''/(a H^4), l = a^(5)/(a H^5); 1+z = a0/a; y = z/(1+z) = 1 - a/a0;
d_L = (a0/a) * a0 * S_K(chi), chi = int_t^{t0} c dt'/a(t'), S_{+1}=sin, S_0=id, S_{-1}=sinh;
Omega0 = 1 + K c^2/(H0^2 a0^2).

Derivation: x = H0 (t0 - t) (dimensionless look-back time), A(x) = a/a0 Taylor-expanded to x^5.
chi = eps * X with eps = c/(a0 H0), X = int_0^x dx'/A(x'). Then
  (H0 a0/c) S_K(eps X) = X - K eps^2 X^3/6 + K^2 eps^4 X^5/120 + O(X^7)
and K eps^2 = Omega0 - 1, K^2 eps^4 = (Omega0-1)^2 for K in {-1,0,1}.
So H0 d_L / c = (1/A) [X - (Om-1) X^3/6 + (Om-1)^2 X^5/120] + O(x^7).
Invert y(x) and expand in y to y^5.
"""
import sympy as sp

q, j, s, l, Om = sp.symbols('q0 j0 s0 l0 Omega0')
x, y, u = sp.symbols('x y u')
N = 6  # keep terms through x^5 / y^5 in H0 dL/c

A = 1 - x - q*x**2/2 - j*x**3/6 + s*x**4/24 - l*x**5/120
yx = sp.expand(1 - A)  # y as series in x

invA = sp.series(1/A, x, 0, N).removeO()
X = sp.integrate(invA, x)
X = sp.expand(X)
def trunc(e, var, n):
    return sp.series(sp.expand(e), var, 0, n).removeO()
F = trunc(invA * (X - (Om-1)*X**3/6 + (Om-1)**2*X**5/120), x, N)

# invert y = y(x): x = sum b_k y^k
bs = sp.symbols('b1:%d' % N)
xy = sum(bs[k-1]*y**k for k in range(1, N))
eq = trunc(yx.subs(x, xy) - y, y, N)
sol = sp.solve([eq.coeff(y, k) for k in range(1, N)], bs, dict=True)[0]
xy = xy.subs(sol)
Fy = trunc(F.subs(x, xy), y, N)
D = [sp.factor(sp.expand(Fy.coeff(y, k+1))) for k in range(N-1)]
Dexp = [sp.expand(d) for d in D]

printed = [
    sp.Integer(1),
    -sp.Rational(1, 2)*(-3 + q),
    -sp.Rational(1, 6)*(12 - 5*q + 3*q**2 - j - Om),
    sp.Rational(1, 24)*(52 - 20*q + 21*q**2 - 15*q**3 - 7*j + 10*q*j + s - 2*Om*(1 + 3*q)),
    sp.Rational(1, 120)*(359 - 184*q + 186*q**2 - 135*q**3 + 105*q**4 + 90*q*j - 105*q**2*j
                         - 15*q*s - 57*j + 10*j**2 + 9*s - l
                         - 5*Om*(17 - 6*q + 9*q**2 - 2*j)),
]

for k in range(5):
    print(f"D{k}_correct =", Dexp[k])
    print(f"  24/120-scaled:", sp.expand(Dexp[k]*[1, 2, 6, 24, 120][k]))
    print(f"  printed - correct =", sp.expand(printed[k] - Dexp[k]),
          " (scaled:", sp.expand((printed[k] - Dexp[k])*[1, 2, 6, 24, 120][k]), ")")

print("factored printed - correct, D3:", sp.factor(sp.expand(printed[3] - Dexp[3])))
print("factored printed - correct, D4:", sp.factor(sp.expand(printed[4] - Dexp[4])))
# alternative reading of the line break '... - 15 q0 s0 + (10.56) - 57 j0 ...' as '+57 j0'
alt4 = printed[4] + sp.Rational(114, 120)*j
print("alt reading (+57 j0) printed - correct, D4:", sp.factor(sp.expand(alt4 - Dexp[4])))
print("flat (Omega0=1) printed - correct, D3, D4:",
      sp.expand((printed[3] - Dexp[3]).subs(Om, 1)), sp.expand((printed[4] - Dexp[4]).subs(Om, 1)))

# ---------- checks against exact models, computed directly (no general formula) ----------
# Only the Taylor data of a at t0 through order 5 (plus K, c, a0) enter the coefficients D0..D4,
# so each model is entered by its Taylor polynomial in tau = t0 - t (exact for polynomial models).
tau = sp.symbols('tau')

def tr(e, n=N + 1):
    e = sp.expand(e)
    return sum(e.coeff(tau, k)*tau**k for k in range(n))

def direct_series(apoly, K, c):
    """apoly: a(t0 - tau) as a polynomial in tau (degree <= 6). Returns D0..D4 and the params."""
    a0 = apoly.subs(tau, 0)
    d = [sp.diff(apoly, tau, n).subs(tau, 0)*(-1)**n for n in range(6)]  # d^n a/dt^n at t0
    H0 = d[1]/a0
    params = {q: -d[2]/a0/H0**2, j: d[3]/a0/H0**3, s: d[4]/a0/H0**4, l: d[5]/a0/H0**5,
              Om: 1 + K*c**2/(H0**2*a0**2)}
    # 1/a(t0-tau) as power series
    r = apoly/a0 - 1
    inv = tr(sum((-r)**k for k in range(N + 1)))/a0
    chi = tr(sp.integrate(c*inv, tau))
    if K == 0:
        Sx = chi
    else:
        Sx = tr(sum((-K)**m*chi**(2*m + 1)/sp.factorial(2*m + 1) for m in range(4)))
    dL = tr(a0*inv*a0*Sx)
    Y = tr(1 - apoly/a0)
    # invert Y(tau) = y by fixed-point iteration tau = (y - (Y - Y1 tau))/Y1
    Y1 = Y.coeff(tau, 1)
    T = y/Y1
    for _ in range(N + 1):
        T = sp.expand((y - (Y - Y1*tau).subs(tau, T))/Y1)
        T = sum(T.coeff(y, k)*y**k for k in range(N + 1))
    G = sp.expand((H0*dL/c).subs(tau, T))
    return [G.coeff(y, k + 1) for k in range(N - 1)], params

tt = tau
models = {
    'Milne a=t, K=-1, c=1, t0=1': ((1 - tt), -1, 1),
    'Milne a=3t, K=-1, c=3, t0=2': (3*(2 - tt), -1, 3),
    'closed de Sitter a=cosh t (Taylor at t0=1/2 to order 6, exact for D0..D4), K=+1, c=1':
        (sum(sp.diff(sp.cosh(sp.Symbol('T')), sp.Symbol('T'), n).subs(sp.Symbol('T'), sp.Rational(1, 2))
             * (-tt)**n/sp.factorial(n) for n in range(7)), 1, 1),
    'toy poly K=+1, c=1/2': (2 + tt*(-1) + tt**2*sp.Rational(1, 3) + tt**3*sp.Rational(2, 7)
                             + tt**4*sp.Rational(1, 5) - tt**5*sp.Rational(3, 11), 1, sp.Rational(1, 2)),
    'toy poly K=-1, c=2': (sp.Rational(3, 2) - tt*sp.Rational(5, 4) - tt**2*sp.Rational(2, 3)
                           + tt**3*sp.Rational(1, 9) - tt**4*sp.Rational(4, 7) + tt**5*sp.Rational(1, 6), -1, 2),
    'toy poly K=0, c=1': (1 - tt*sp.Rational(1, 2) + tt**2*sp.Rational(1, 5) - tt**3
                          + tt**4*sp.Rational(1, 3) + tt**5*sp.Rational(1, 8), 0, 1),
}
print()
for name, (ap, K, c) in models.items():
    coeffs, params = direct_series(sp.expand(ap), K, c)
    gen = [dd.subs(params) for dd in Dexp]
    pr = [sp.simplify(dd.subs(params)) for dd in printed]
    print(name, {str(k): sp.simplify(v) for k, v in params.items()})
    for k in range(5):
        ok = abs(sp.N(coeffs[k] - gen[k], 50)) < 1e-40
        print(f"  D{k}: direct={sp.N(coeffs[k], 15)}  general={sp.N(gen[k], 15)}  match={ok}  printed={sp.N(pr[k], 15)}  printed==direct: {abs(sp.N(pr[k]-coeffs[k], 50)) < 1e-40}")
