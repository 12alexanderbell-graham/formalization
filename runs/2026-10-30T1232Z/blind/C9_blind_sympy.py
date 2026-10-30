#!/usr/bin/env python3
"""Blind, independent derivation of the z-series of H0*d_L/c and H0*d_A/c
with spatial curvature, to compare with Bamba-Capozziello-Nojiri-Odintsov
(arXiv:1205.3421v3) Eqs. (10.38)-(10.51).

Definitions used (from the source, Eqs. (10.1)-(10.5), (10.26)-(10.28)):
  a(t)/a0 = 1 + x - q0 x^2/2 + j0 x^3/3! + s0 x^4/4! + l0 x^5/5! + O(x^6),
            x = H0 (t - t0)          (x < 0 in the past)
  1 + z   = a0 / a(t)
  chi     = int_t^t0 c dt'/a(t')     (dimensionless comoving coordinate distance)
  r0      = S_K(chi) = sin(sqrt(K) chi)/sqrt(K)  (K=1: sin, K=0: chi, K=-1: sinh)
  d_L     = (a0/a(t)) a0 r0 ,   d_A = (a(t)/a0) a0 r0
Dimensionless reduction: u = int_x^0 dx'/A(x') with A = a/a0, then
  chi = c u /(H0 a0),  H0 a0 r0 / c = S_k(u),  k := K c^2/(H0^2 a0^2),
so H0 d_L / c = S_k(u)/A and H0 d_A / c = A S_k(u), functions of q0,j0,s0,l0,k only.
We write H0 d/c = z * (D0 + D1 z + D2 z^2 + D3 z^3 + D4 z^4) + O(z^6).
"""
import sympy as sp

x, z = sp.symbols('x z')
q, j, s, l, k = sp.symbols('q0 j0 s0 l0 k')  # k = K c^2/(H0^2 a0^2)
N = 6  # work to O(x^6), i.e. through x^5

A = 1 + x - q*x**2/2 + j*x**3/6 + s*x**4/24 + l*x**5/120


def trunc(expr, var, n=N):
    """Keep terms of degree < n in var."""
    p = sp.Poly(sp.expand(expr), var)
    return sum(c*var**m[0] for m, c in zip(p.monoms(), p.coeffs()) if m[0] < n)


def series(expr, var, n=N):
    return trunc(sp.series(expr, var, 0, n).removeO(), var, n)


# 1/A as series in x
invA = series(1/A, x)
# u(x) = int_x^0 dx'/A  = -int_0^x invA
u = -sp.integrate(invA, (x, 0, x))
u = trunc(u, x)
# S_k(u) = u - k u^3/6 + k^2 u^5/120 - ...
Sk = trunc(u - k*u**3/6 + k**2*u**5/120, x)

dL_x = trunc(sp.expand(Sk*invA), x)   # H0 dL / c as series in x
dA_x = trunc(sp.expand(Sk*A), x)      # H0 dA / c as series in x

# z(x) = 1/A - 1; invert x(z) = sum b_n z^n, n=1..5
zx = sp.expand(invA - 1)
bs = sp.symbols('b1:6')
xz = sum(bs[i]*z**(i+1) for i in range(5))
eq = trunc(sp.expand(zx.subs(x, xz)), z) - z
sol = {}
for n in range(1, 6):
    cn = sp.expand(sp.Poly(eq, z).coeff_monomial(z**n)).subs(sol)
    bn = bs[n-1]
    sol[bn] = sp.simplify(sp.solve(sp.Eq(cn, 0), bn)[0])
xz = sp.expand(xz.subs(sol))
print("x(z) = H0 (t - t0) as series in z:")
for n in range(1, 6):
    print(f"  z^{n}:", sp.factor(sp.Poly(xz, z).coeff_monomial(z**n)))

dL_z = trunc(sp.expand(dL_x.subs(x, xz)), z)
dA_z = trunc(sp.expand(dA_x.subs(x, xz)), z)


def coeffs(ser):
    P = sp.Poly(ser, z)
    return [sp.expand(P.coeff_monomial(z**(n+1))) for n in range(5)]


DL = coeffs(dL_z)
DA = coeffs(dA_z)

# Printed coefficients (10.39)-(10.44), (10.46)-(10.51), with "j^2" read as j0^2
R = sp.Rational
DLp = [
    sp.Integer(1),
    -R(1, 2)*(-1 + q),
    -R(1, 6)*(1 - q - 3*q**2 + j + k),
    R(1, 24)*(2 - 2*q - 15*q**2 - 15*q**3 + 5*j + 10*q*j + s + 2*k*(1 + 3*q)),
    R(1, 120)*(-6 + 6*q + 81*q**2 + 165*q**3 + 105*q**4 - 110*q*j - 105*q**2*j
               - 15*q*s - 27*j + 10*j**2 - 11*s - l - 5*k*(1 + 8*q + 9*q**2 - 2*j)),
]
DAp = [
    sp.Integer(1),
    -R(1, 2)*(3 + q),
    R(1, 6)*(11 + 7*q + 3*q**2 - j - k),
    -R(1, 24)*(50 + 46*q + 39*q**2 + 15*q**3 - 13*j - 10*q*j - s - 2*k*(5 + 3*q)),
    R(1, 120)*(274 + 326*q + 411*q**2 + 315*q**3 + 105*q**4 - 210*q*j - 105*q**2*j
               - 15*q*s - 137*j + 10*j**2 - 21*s - l - 5*k*(17 + 20*q + 9*q**2 - 2*j)),
]


def show(name, correct, printed):
    print(f"\n===== {name} (coefficient of z^(n+1) in H0 d/c; k = K c^2/(H0^2 a0^2)) =====")
    for n in range(5):
        c = correct[n]
        d = sp.expand(printed[n] - c)
        print(f"D^{n} correct          = {sp.collect(c, k)}")
        print(f"D^{n} correct (x{[1,2,6,24,120][n]}) = {sp.collect(sp.expand(c*[1,2,6,24,120][n]), k)}")
        print(f"D^{n} printed - correct = {sp.collect(d, k)}"
              + ("   [OK]" if d == 0 else "   [MISMATCH]"))


show("Luminosity distance d_L", DL, DLp)
show("Angular-diameter distance d_A", DA, DAp)

# Consistency: d_A = d_L/(1+z)^2 exactly
chk = trunc(sp.expand(dA_z - trunc(sp.expand(dL_z*series(1/(1+z)**2, z)), z)), z)
print("\nIdentity check  d_A - d_L/(1+z)^2 (to z^5):", sp.simplify(chk))

# Also: does the printed d_A satisfy d_A = d_L/(1+z)^2 with the printed d_L?
pL = sum(DLp[n]*z**(n+1) for n in range(5))
pA = sum(DAp[n]*z**(n+1) for n in range(5))
pchk = trunc(sp.expand(pA - pL*series(1/(1+z)**2, z)), z)
print("Printed d_A - printed d_L/(1+z)^2 (to z^5):", sp.collect(sp.expand(pchk), z))

# ---- Exact-model checks ----
print("\n===== Exact model checks =====")
models = {
    # Milne: a = t, t0 = 1, K = -1 (c = 1): H0 = 1, a0 = 1, q=j=s=l=0, k = -1
    "Milne a=t, K=-1": ({q: 0, j: 0, s: 0, l: 0, k: -1}, z + z**2/2),
    # flat de Sitter: a = e^t, K = 0: q=-1, j=s=l=1, k=0; H0 dL/c = z(1+z)
    "de Sitter a=e^t, K=0": ({q: -1, j: 1, s: 1, l: 1, k: 0}, z + z**2),
    # closed de Sitter a = cosh t at t0 = 0 is singular (H0=0); use t0 = 1:
}
for name, (sub, exact_dL) in models.items():
    corr = sp.expand(sum(DL[n].subs(sub)*z**(n+1) for n in range(5)))
    prin = sp.expand(sum(DLp[n].subs(sub)*z**(n+1) for n in range(5)))
    ex = trunc(sp.expand(series(exact_dL, z)), z)
    exA = trunc(sp.expand(series(exact_dL/(1+z)**2, z)), z)
    corrA = sp.expand(sum(DA[n].subs(sub)*z**(n+1) for n in range(5)))
    prinA = sp.expand(sum(DAp[n].subs(sub)*z**(n+1) for n in range(5)))
    print(f"\n{name}:")
    print("  exact   H0 dL/c =", ex)
    print("  derived H0 dL/c =", corr, "  derived-exact:", sp.expand(corr - ex))
    print("  printed H0 dL/c =", prin, "  printed-exact:", sp.expand(prin - ex))
    print("  exact   H0 dA/c =", exA)
    print("  derived-exact (dA):", sp.expand(corrA - exA))
    print("  printed-exact (dA):", sp.expand(prinA - exA))

# Independent numerical check in a non-trivial model: closed (K=+1) model
# a(t) = cosh(t) (c=1) at t0 = 1 -- solves a'' = a; exact chi = 2(atan(e^t0)-atan(e^t)).
print("\n===== Numeric check: a = cosh t, t0 = 1, K = +1, c = 1 =====")
t = sp.symbols('t')
a_ex = sp.cosh(t)
t0 = 1
a0 = a_ex.subs(t, t0)
H0v = (sp.diff(a_ex, t)/a_ex).subs(t, t0)
pars = {}
for name_, n in ((q, 2), (j, 3), (s, 4), (l, 5)):
    val = (sp.diff(a_ex, t, n)/a_ex).subs(t, t0)/H0v**n
    pars[name_] = -val if n == 2 else val
pars[k] = 1/(H0v**2*a0**2)
zz = sp.Rational(1, 100)
# solve a0/a(t) = 1+z
tv = sp.nsolve(a0/a_ex - (1+zz), t, 0.99, prec=50)
chi = sp.Integral(1/a_ex, (t, tv, t0)).evalf(50)
dL_exact = (a0/a_ex.subs(t, tv))*a0*sp.sin(chi)
lhs = (H0v*dL_exact).evalf(50)
corr = sum(DL[n].subs(pars)*zz**(n+1) for n in range(5)).evalf(50)
prin = sum(DLp[n].subs(pars)*zz**(n+1) for n in range(5)).evalf(50)
print(f"z = {zz}: exact H0 dL = {sp.N(lhs, 25)}")
print(f"  derived series error  = {sp.N(lhs-corr, 6)}   (expect ~ z^6 = 1e-12)")
print(f"  printed series error  = {sp.N(lhs-prin, 6)}")
