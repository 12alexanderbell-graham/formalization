"""Referee: facts behind the claim that vdW_coexistence_unique needs only a != 0 (hR, hb, hl removable).
Reduced isotherm (R != 0, b != 0, a != 0):  P(v) = (a/(27 b^2)) * g(v/b),  g(x) = (28/5)/(x-1) - 27/x^2.
Lean junk values: g(1) = -27 (division by 0), g(0) = -28/5.
"""
import sympy as sp
x = sp.symbols('x', real=True)
g = sp.Rational(28, 5)/(x - 1) - 27/x**2
dg = sp.together(sp.diff(g, x))
print("g' =", sp.factor(dg))
# zeros of g (pi = 0 candidates): 28 x^2 - 135 x + 135 = 0
print("zeros of g:", [sp.N(r, 8) for r in sp.solve(sp.numer(sp.together(g)), x)], " (both > 1)")
# critical points of g: 14x^3 - 135x^2 + 270x - 135 = 0 (numerator of g' up to sign/factor)
s = 14*x**3 - 135*x**2 + 270*x - 135
print("critical points of g:", [sp.N(r, 8) for r in sp.real_roots(sp.Poly(s, x))])
# on (0,1): exactly one critical point -> g unimodal (max) there; on (-oo,0): g' < 0 (no critical point)
rr = [sp.N(r, 8) for r in sp.real_roots(sp.Poly(s, x))]
print("critical points in (0,1):", [r for r in rr if 0 < r < 1], " in (-oo,0):", [r for r in rr if r < 0])
print("g < 0 on x < 1, x != 0 (both terms negative): g(-5), g(0.5) =", sp.N(g.subs(x, -5)), sp.N(g.subs(x, sp.Rational(1, 2))))
print("junk g(1) = -27, g(0) = -28/5 (Lean: t/0 = 0)")
