"""Blind derivation of the flat (K=0) d_L(y) series, c = 1.

a(t0 + tau) = a0 [1 + H0 tau - q0 H0^2 tau^2/2 + j0 H0^3 tau^3/6 + s0 H0^4 tau^4/24 + ...]
  (this is just Taylor's theorem with H = a'/a, q = -a''/(a H^2), j = a'''/(a H^3), s = a''''/(a H^4))
1 + z = a0/a(t),  y = z/(1+z) = 1 - a(t)/a0
d_L(t) = (a0/a(t)) * a0 * int_t^{t0} ds / a(s)          (Eqs. 10.26, 10.28 with K = 0, c = 1)
Expand H0 d_L as a power series in y and compare with y[1 + D1 y + D2 y^2 + ...].
"""
import sympy as sp

tau, s, y, H0, a0, q0, j0, s0 = sp.symbols('tau s y H0 a0 q0 j0 s0')
N = 5  # order in tau

def A(x):
    return a0 * (1 + H0*x - q0*H0**2*x**2/2 + j0*H0**3*x**3/6 + s0*H0**4*x**4/24)

# int_{t0+tau}^{t0} ds/a(s) = -int_0^{tau} dx / A(x)
inv = sp.series(1/A(s), s, 0, N).removeO()
chi = -sp.integrate(inv, (s, 0, tau))
dL = sp.series(a0 / A(tau) * a0 * chi, tau, 0, N).removeO()
yt = sp.expand(1 - A(tau)/a0)                     # y as a function of tau (y ~ -H0 tau)

# invert y(tau) -> tau(y) by undetermined coefficients
cs = sp.symbols('c1:%d' % N)
tau_y = sum(cs[k]*y**(k+1) for k in range(N-1))
eqs = sp.Poly(sp.series(yt.subs(tau, tau_y) - y, y, 0, N).removeO(), y).all_coeffs()
sol = sp.solve(eqs, cs, dict=True)[0]
tau_y = tau_y.subs(sol)
dLy = sp.series(sp.expand(H0 * dL.subs(tau, tau_y)), y, 0, N).removeO()
dLy = sp.expand(dLy)
c1 = sp.simplify(dLy.coeff(y, 1))
c2 = sp.factor(dLy.coeff(y, 2))
c3 = sp.expand(dLy.coeff(y, 3))
print('H0 d_L = c1 y + c2 y^2 + c3 y^3 + O(y^4)')
print('c1 =', c1)
print('c2 = D1 =', c2)
print('c3 = D2 =', c3)
print('6*D2 =', sp.expand(6*c3))
Om = 1
printedD1 = -sp.Rational(1, 2)*(-3 + q0)
printedD2 = -sp.Rational(1, 6)*(12 - 5*q0 + 3*q0**2 - j0 - Om)
CVD2 = sp.Rational(1, 6)*(12 - 5*q0 + 3*q0**2 - (j0 + Om))
print('D1 - printed D1 =', sp.simplify(c2 - printedD1))
print('D2 - printed D2 =', sp.expand(c3 - printedD2))
print('D2 - Cattoen-Visser (52) D2 (Omega0=1) =', sp.expand(c3 - CVD2))
# de Sitter check: q0=-1, j0=1
print('de Sitter: correct D2 =', c3.subs({q0: -1, j0: 1}), ', printed D2 =', printedD2.subs({q0: -1, j0: 1}))
