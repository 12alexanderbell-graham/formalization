"""Referee: rigorous enclosure of the vdW saturation pressure at T_r = 0.7 and the acentric factor.

Reduced variables x = v/b, pi = p/P_c.  With R T = (7/10)(8a/(27b)) and P_c = a/(27 b^2):
    g(x) = P/P_c = (28/5)/(x-1) - 27/x^2           (= 8T_r/(3 v_r - 1) - 3/v_r^2, v_r = x/3)
    G(x) = (28/5) log(x-1) + 27/x                  (antiderivative of g on x > 1)
Maxwell:  g(x1) = g(x3) = pi,  G(x3) - G(x1) = pi (x3 - x1).
g(x) = pi  <=>  c_pi(x) := 5 pi x^3 - (5 pi + 28) x^2 + 135 x - 135 = 0   (x > 1).
Residual F(pi) = G(x3(pi)) - G(x1(pi)) - pi (x3 - x1), strictly decreasing on (0, g(x_max)).
Roots are enclosed by exact-rational bisection (Fraction), logs by mpmath.iv (outward rounding).
"""
from fractions import Fraction as Q
import mpmath
from mpmath import iv, mp

iv.prec = 300
mp.prec = 300
def lo_(X): return mp.make_mpf(X._mpi_[0])
def hi_(X): return mp.make_mpf(X._mpi_[1])

def cub(pi, x):
    return 5*pi*x**3 - (5*pi + 28)*x**2 + 135*x - 135

def bisect(f, lo, hi, n=160):
    flo, fhi = f(lo), f(hi)
    assert flo * fhi < 0, (float(lo), float(hi), float(flo), float(fhi))
    for _ in range(n):
        m = (lo + hi) / 2
        fm = f(m)
        if fm == 0:
            return m, m
        if (fm < 0) == (flo < 0):
            lo, flo = m, fm
        else:
            hi, fhi = m, fm
    return lo, hi

def ivq(q):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)

# --- spinodals: g'(x) = 0  <=>  s(x) = 14x^3 - 135x^2 + 270x - 135 = 0
s = lambda x: 14*x**3 - 135*x**2 + 270*x - 135
xmin = bisect(s, Q(3, 2), Q(2))      # s(1) = 14 > 0, s(3/2) < 0 ... checked by assert
xmax = bisect(s, Q(5), Q(8))
def g_iv(X):
    return iv.mpf(28)/5/(X - 1) - 27/X**2
gmin = g_iv(iv.mpf([ivq(xmin[0]), ivq(xmin[1])]))
gmax = g_iv(iv.mpf([ivq(xmax[0]), ivq(xmax[1])]))
print("spinodal x_min in", [float(t) for t in xmin], " g(x_min) in", mpmath.nstr(lo_(gmin), 12), mpmath.nstr(hi_(gmin), 12))
print("spinodal x_max in", [float(t) for t in xmax], " g(x_max) in", mpmath.nstr(lo_(gmax), 12), mpmath.nstr(hi_(gmax), 12))
print("s(1) =", s(Q(1)), "> 0, s has exactly the roots x_min, x_max on (1,oo) (third root <1):",
      bisect(s, Q(0), Q(1))[0] < 1)

def roots(pi):
    """Enclose the outer roots x1 in (1, x_min), x3 in (x_max, oo) of g = pi (pi in (0, g_max))."""
    f = lambda x: cub(pi, x)
    r1 = bisect(f, Q(1), xmin[0])
    hi = xmax[1]
    while f(hi) * f(xmax[1]) > 0 or f(hi) == 0:
        hi *= 2
    r3 = bisect(f, xmax[1], hi)
    return r1, r3

def F_iv(pi):
    (a1, b1), (a3, b3) = roots(pi)
    X1 = iv.mpf([ivq(a1), ivq(b1)])
    X3 = iv.mpf([ivq(a3), ivq(b3)])
    P = ivq(pi)
    G = lambda X: iv.mpf(28)/5*iv.log(X - 1) + 27/X
    return G(X3) - G(X1) - P*(X3 - X1), (a1, b1), (a3, b3)

for name, pi in [("pi_lo = 0.200455", Q(200455, 10**6)), ("pi_hi = 0.200465", Q(200465, 10**6))]:
    F, r1, r3 = F_iv(pi)
    print(name, " x1 ~", mpmath.nstr(mpmath.mpf(r1[0].numerator)/r1[0].denominator, 12),
          " x3 ~", mpmath.nstr(mpmath.mpf(r3[0].numerator)/r3[0].denominator, 12), " F in", mpmath.nstr(lo_(F), 10), "..", mpmath.nstr(hi_(F), 10))

# --- tight enclosure of pi* by bisection on the sign of the (rigorous) residual
lo, hi = Q(200455, 10**6), Q(200465, 10**6)
assert lo_(F_iv(lo)[0]) > 0 and hi_(F_iv(hi)[0]) < 0
for _ in range(70):
    m = (lo + hi) / 2
    F = F_iv(m)[0]
    if lo_(F) > 0:
        lo = m
    elif hi_(F) < 0:
        hi = m
    else:
        break
PI = iv.mpf([ivq(lo), ivq(hi)])
print("\npi* = p_s/P_c in", mpmath.nstr(lo_(PI), 25), "..", mpmath.nstr(hi_(PI), 25))
(a1, b1), (a3, b3) = roots(lo)
(c1, d1), (c3, d3) = roots(hi)
print("x_l = v_l/b in", float(c1), "..", float(b1), " (v_l/v_c = x/3 ~", float(b1) / 3, ")")
print("x_g = v_g/b in", float(c3), "..", float(b3), " (v_g/v_c ~", float(b3) / 3, ")")
print("margin to 0.200455 :", mpmath.nstr(lo_(PI - iv.mpf('0.200455')), 6))
print("margin to 0.200465 :", mpmath.nstr(lo_(iv.mpf('0.200465') - PI), 6))
OM = -iv.log(PI)/iv.log(10) - 1
print("omega in", mpmath.nstr(lo_(OM), 20), "..", mpmath.nstr(hi_(OM), 20))
print("margin to -0.30205 :", mpmath.nstr(lo_(OM + iv.mpf('0.30205')), 6))
print("margin to -0.30195 :", mpmath.nstr(lo_(iv.mpf('-0.30195') - OM), 6))
# pi values at which omega hits its rounding boundaries
print("omega = -0.30195 at pi =", mpmath.nstr(mpmath.power(10, -mpmath.mpf('0.69805')), 12),
      "; omega = -0.30205 at pi =", mpmath.nstr(mpmath.power(10, -mpmath.mpf('0.69795')), 12))
