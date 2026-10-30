"""Blind recomputation of l0 for flat matter + CPL dark energy (Capozziello-Lazkoz-Salzano, Eq. 17/22).

Method: work in x = 1+z = a0/a (a0 = 1, H0 = 1). Then a = 1/x and d/dt acting on any
function of x is D f = -x H(x) f'(x) with H(x) = sqrt(E2(x)).  Then
  q0 = -a''/(a H^2), j0 = a'''/(a H^3), s0 = a''''/(a H^4), l0 = a^(5)/(a H^5)  at x = 1.
Cross-check: numerically integrate da/dt = a H(1/a) (mpmath Taylor ODE solver) and take
a one-sided 5th derivative at t0; compare with the symbolic result and the printed Eq. (22).
"""
import sympy as sp

Om, w0, wa, x, t = sp.symbols('Omega_m w0 wa x t', real=True)

E2 = Om * x**3 + (1 - Om) * x**(3 * (1 + w0 + wa)) * sp.exp(-3 * wa * (x - 1) / x)
# derivatives of E2 at x = 1 (x**(real) evaluates to 1 at x = 1)
F = sp.Function('F')
Fvals = {sp.Derivative(F(x), (x, k)).subs(x, 1) if k else F(1): sp.expand(sp.diff(E2, x, k).subs(x, 1))
         for k in range(6)}
H = sp.sqrt(F(x))

def D(f):
    return sp.expand(-x * H * sp.diff(f, x))

derivs = [1 / x]
for _ in range(5):
    derivs.append(D(derivs[-1]))

def evalx1(e):
    e = e.subs(x, 1).doit()
    # replace highest derivatives first
    for k in range(5, 0, -1):
        e = e.subs(sp.Subs(sp.Derivative(F(x), (x, k)), x, 1), Fvals[sp.Derivative(F(x), (x, k)).subs(x, 1)])
        e = e.subs(sp.Derivative(F(x), (x, k)).subs(x, 1), Fvals[sp.Derivative(F(x), (x, k)).subs(x, 1)])
    e = e.subs(F(1), 1)
    return sp.expand(e)

def coeff(n):
    # a = 1/x -> 1 at x=1, H(1) = 1
    return evalx1(derivs[n])

q0 = sp.expand(-coeff(2))
j0 = coeff(3)
s0 = coeff(4)
l0 = coeff(5)

printed_q0 = sp.Rational(1, 2) + sp.Rational(3, 2) * (1 - Om) * w0
printed_j0 = 1 + sp.Rational(3, 2) * (1 - Om) * (3 * w0 * (1 + w0) + wa)
printed_l0 = (sp.Rational(35, 2)
              + (1 - Om) / 4 * (213 + (7 - Om) * wa) * wa
              + (1 - Om) / 4 * (489 + 9 * (82 - 21 * Om) * wa) * w0
              + sp.Rational(9, 2) * (1 - Om) * (67 - 21 * Om + sp.Rational(3, 2) * (23 - 11 * Om) * wa) * w0**2
              + sp.Rational(27, 4) * (1 - Om) * (47 - 24 * Om) * w0**3
              + sp.Rational(81, 2) * (1 - Om) * (3 - 2 * Om) * w0**4)

# --- independent cross-check: numerical Taylor coefficients of the ODE solution
# da/dt = a * sqrt(E2(1/a)), a(0)=1 (H0=1), via mpmath's Taylor-series ODE solver.
import mpmath as mp
def l0_numeric(Omv, w0v, wav):
    mp.mp.dps = 30
    def Hof(a):
        xx = 1 / a
        return mp.sqrt(Omv * xx**3 + (1 - Omv) * xx**(3 * (1 + w0v + wav)) * mp.exp(-3 * wav * (xx - 1) / xx))
    fwd = mp.odefun(lambda tt, a: a * Hof(a), 0, mp.mpf(1))    # t >= t0
    bwd = mp.odefun(lambda tt, a: -a * Hof(a), 0, mp.mpf(1))   # a(t0 - s)
    g = lambda tt: fwd(tt) if tt >= 0 else bwd(-tt)
    d1 = mp.diff(g, 0, 5, h=mp.mpf('0.02'))
    d2 = mp.diff(g, 0, 5, h=mp.mpf('0.01'))
    return (4 * d2 - d1) / 3   # Richardson extrapolation (central differences, O(h^2))

if __name__ == '__main__':
    print('q0 true      :', sp.factor(q0), '| printed matches:', sp.expand(q0 - printed_q0) == 0)
    print('j0 true      :', sp.factor(j0), '| printed matches:', sp.expand(j0 - printed_j0) == 0)
    for vals in [(0.3, -0.9, 0.2), (0.25, -1.1, -0.4)]:
        num = l0_numeric(*[mp.mpf(v) for v in vals])
        sym = l0.subs({Om: sp.Rational(str(vals[0])), w0: sp.Rational(str(vals[1])), wa: sp.Rational(str(vals[2]))})
        pr = printed_l0.subs({Om: sp.Rational(str(vals[0])), w0: sp.Rational(str(vals[1])), wa: sp.Rational(str(vals[2]))})
        print('numeric check at', vals, ': ODE l0 =', mp.nstr(num, 15), ' symbolic true =', float(sym), ' printed =', float(pr))
    print('l0 true (expanded):')
    print('  ', sp.collect(l0, [w0, wa], evaluate=True))
    print('l0 true as poly in w0, wa with factored coefficients:')
    P = sp.Poly(l0, w0, wa)
    for mon, c in sorted(P.terms(), reverse=True):
        print('   w0^%d wa^%d :' % mon, sp.factor(c))
    diff = sp.expand(printed_l0 - l0)
    print('printed - true (expanded):', diff)
    print('printed - true (factored):', sp.factor(diff))
