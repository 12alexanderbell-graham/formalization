"""Blind derivation of the y-series of the deceleration distance d_Q = d_L/(1+z)^{3/2}
for a spatially flat FLRW model (c = 1), independent of the paper.

Method: Taylor-expand a(t) about t0 in tau = t - t0 (tau < 0 for emission in the past):
    a(t)/a0 = 1 + H tau + (1/2)(-q H^2) tau^2 + (1/6) j H^3 tau^3 + (1/24) s H^4 tau^4 + ...
(using H = a'/a, q = -a''/(a H^2), j = a'''/(a H^3) at t0).  Then
    1 + z = a0/a(t),   y = z/(1+z) = 1 - a(t)/a0,
    d_L   = a0 (1+z) * int_t^{t0} dt'/a(t'),
    d_Q   = d_L (1+z)^{-3/2}.
Invert y(tau) as a series, substitute, and read off H0 d_Q as a series in y.
Also checks de Sitter (a = e^t) exactly.
"""
import sympy as sp

tau, T, y, H, q, j, s = sp.symbols('tau T y H q j s', real=True)
N = 5  # order in tau

# a(t0 + tau)/a0
A = 1 + H*tau - q*H**2*tau**2/2 + j*H**3*tau**3/6 + s*H**4*tau**4/24
A = sp.expand(A)

# int_{t}^{t0} dt'/a(t') * a0 = int_{tau}^{0} dT / A(T)
invA = sp.series(1/A.subs(tau, T), T, 0, N).removeO()
I = sp.integrate(invA, (T, tau, 0))
onepz = sp.series(1/A, tau, 0, N).removeO()
dL = sp.expand(sp.series(onepz*I, tau, 0, N).removeO())

yy = sp.expand(1 - A)  # y as a function of tau
# invert: tau = sum c_k y^k
c = sp.symbols('c1:5')
tau_y = sum(c[k]*y**(k+1) for k in range(4))
eq = sp.expand(sp.series(yy.subs(tau, tau_y), y, 0, 5).removeO() - y)
sol = sp.solve([eq.coeff(y, k) for k in range(1, 5)], c, dict=True)[0]
tau_y = tau_y.subs(sol)

# (1+z) = 1/(1-y) exactly, so d_Q = d_L (1-y)^{3/2}
dL_y = sp.series(dL.subs(tau, tau_y), y, 0, 4).removeO()
dQ_y = sp.expand(sp.series(dL_y*(1-y)**sp.Rational(3, 2), y, 0, 4).removeO())
HdQ = sp.expand(H*dQ_y)
coeffs = [sp.simplify(HdQ.coeff(y, k)) for k in range(1, 4)]
print("H0*d_L(y) =", sp.collect(sp.expand(H*dL_y), y))
print("H0*d_Q(y) coefficients of y, y^2, y^3:")
for k, cf in enumerate(coeffs, 1):
    print(f"  y^{k}:", sp.factor(cf))

Om = sp.Integer(1)  # flat: Omega0 = 1
derived = coeffs[2]
correct_formula = sp.Rational(1, 24)*(3 - 2*q + 12*q**2 - 4*(j + Om))
printed_formula = sp.Rational(1, 12)*(3 - 2*q + 12*q**2 - 4*(j + Om))
print("derived y^3 coeff (=Q^2) minus (1/24)[3-2q+12q^2-4(j+1)]:", sp.simplify(derived - correct_formula))
print("derived minus printed (1/12)[...]:", sp.factor(sp.simplify(derived - printed_formula)))
assert sp.simplify(coeffs[0] - 1) == 0
assert sp.simplify(coeffs[1] + q/2) == 0
assert sp.simplify(derived - correct_formula) == 0

# de Sitter a = e^t, H = 1, q = -1, j = 1: exact d_Q = y (1-y)^{-1/2}
dS = sp.series(y*(1-y)**sp.Rational(-1, 2), y, 0, 5)
print("de Sitter exact H0 d_Q =", dS)
print("de Sitter printed Q^2 =", printed_formula.subs({q: -1, j: 1}),
      " correct Q^2 =", correct_formula.subs({q: -1, j: 1}))
