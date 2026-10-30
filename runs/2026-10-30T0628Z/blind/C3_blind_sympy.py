"""Blind check of Eq. (A2), arXiv:0802.1583v2 (Capozziello-Cardone-Salzano), Appendix A.

Setup (from the source text only):
  a(t)/a(t0) = 1 + H0 T - q0/2 H0^2 T^2 + j0/6 H0^3 T^3 + s0/24 H0^4 T^4 + l0/120 H0^5 T^5 + O(T^6),
  T = t - t0,  1 + z = a(t0)/a(t),  D = c (t0 - t*)  so  T = -D/c at emission.
Let x = H0 D / c (dimensionless).  Then
  1/(1+z) = 1 - x - q0/2 x^2 - j0/6 x^3 + s0/24 x^4 - l0/120 x^5 + O(x^6).
Invert to x(z) = z * (D0 + D1 z + D2 z^2 + D3 z^3 + D4 z^4) + O(z^6).
"""
import sympy as sp

z, x, q, j, s, l = sp.symbols('z x q0 j0 s0 l0')
N = 6  # need x through z^5

# a/a0 as a series in x (T = -x/H0)
A = 1 - x - q/2*x**2 - j/6*x**3 + s/24*x**4 - l/120*x**5

# Unknown series x(z) = sum_{k=1}^{5} c_k z^k
c = sp.symbols('c1:6')
X = sum(c[k-1]*z**k for k in range(1, N))
eq = sp.expand(A.subs(x, X) - 1/(1+z))
ser = sp.series(eq, z, 0, N).removeO()
sol = {}
for k in range(1, N):
    coeff = sp.expand(ser.coeff(z, k).subs(sol))
    ck = sp.solve(coeff, c[k-1])[0]
    sol[c[k-1]] = sp.expand(ck)

derived = [sp.expand(sol[c[k]]) for k in range(5)]

R = sp.Rational
printed = [
    sp.Integer(1),
    -(1 + q/2),
    1 + q + q**2/2 - j/6,
    -(1 + R(3, 2)*q + R(3, 2)*q**2 + R(5, 8)*q**3 - R(1, 2)*j - R(5, 12)*q*j - s/24),
    1 + 2*q + 3*q**2 + R(5, 2)*q**3 + R(7, 2)*q**4 - R(5, 3)*q*j - R(7, 8)*q**2*j - j
      + j**2/12 - R(1, 8)*q*s - s/6 - l/120,
]

for k in range(5):
    d = sp.expand(derived[k]); p = sp.expand(printed[k])
    print(f"D{k}_z derived : {d}")
    print(f"D{k}_z printed : {p}")
    print(f"   derived - printed = {sp.expand(d - p)}")
    print()

# Term-by-term comparison for D4
def terms(e):
    return sp.Poly(sp.expand(e), q, j, s, l).as_dict()
td, tp = terms(derived[4]), terms(printed[4])
print("D4 term-by-term (monomial exponents (q0,j0,s0,l0): derived | printed)")
for m in sorted(set(td) | set(tp), key=lambda m: (sum(m), m)):
    a_, b_ = td.get(m, 0), tp.get(m, 0)
    mono = sp.Mul(*[v**e for v, e in zip((q, j, s, l), m)])
    flag = "" if a_ == b_ else "   <-- MISMATCH"
    print(f"  {str(mono):12s}: {str(a_):8s} | {str(b_):8s}{flag}")

# Independent cross-check: substitute a numeric model (de Sitter-like / power law) and
# compare against exact x(z).  Power law a ~ t^p: H = p/t, q = 1/p - 1, j,s,l from derivatives.
tt, p = sp.symbols('t p', positive=True)
a = tt**p
H = sp.diff(a, tt)/a
par = [sp.simplify(sp.diff(a, tt, n)/a/H**n) for n in range(1, 6)]
qv, jv, sv, lv = -par[1], par[2], par[3], par[4]
pv = R(2, 3)  # matter-dominated
subs = {q: qv.subs(p, pv), j: jv.subs(p, pv), s: sv.subs(p, pv), l: lv.subs(p, pv)}
# exact: 1+z = (t0/t)^p, D = c(t0 - t), H0 = p/t0 -> x = p(1 - (1+z)^(-1/p))
x_exact = pv*(1 - (1+z)**(-1/pv))
ex = sp.series(x_exact, z, 0, 6).removeO()
for k in range(5):
    assert sp.simplify(ex.coeff(z, k+1) - derived[k].subs(subs)) == 0, k
print("\nCross-check vs exact matter-dominated power law (p=2/3): derived coefficients OK")
print("printed D4 at p=2/3:", printed[4].subs(subs), " exact:", ex.coeff(z, 5))
