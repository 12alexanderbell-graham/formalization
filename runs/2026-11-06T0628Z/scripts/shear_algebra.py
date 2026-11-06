# Algebra of the one-sided bound for Robertson in sheared coordinates (u2, u3) = (y2, y3 + c*y2),
# weight w*e2^2 + k^2 with k = e3 + c*e2 (prepares the generalisation of rob_onesided; sympy only).
import sympy as sp
x2, x3, h2, k, c, w, k1, k2, k3 = sp.symbols('x2 x3 h2 k c w k1 k2 k3', real=True)
P = lambda a, b: k1*(1 - a - b) - k2*a*b - k3*a**2
Q = lambda a, b: k3*a**2
h3 = k - c*h2
dP = sp.expand(P(x2 + h2, x3 + h3) - P(x2, x3))
dQ = sp.expand(Q(x2 + h2, x3 + h3) - Q(x2, x3))
lhs = sp.expand(w*dP*h2 + (dQ + c*dP)*k)
poly = sp.Poly(lhs, h2, k)
for mon, co in sorted(poly.terms(), key=lambda t: sum(t[0])):
    print(mon, sp.factor(co))
