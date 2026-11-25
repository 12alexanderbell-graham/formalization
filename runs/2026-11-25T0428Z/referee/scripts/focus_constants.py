"""Check the Jordan-basis claims and the O(sqrt Nw) constants at the focus (1,2).

x = u-1, y = v-2:  x' = -x - y - x(x+y),  y' = 2x + xy   (t = log s).
Q = 7x^2 + (x+2y)^2,  p = sqrt7 x,  q = x + 2y,  Q = p^2 + q^2.
"""
import sympy as sp
import mpmath as mp

x, y, p, q, th = sp.symbols("x y p q theta", real=True)
N1 = -x * (x + y)
N2 = x * y
xd = -x - y + N1
yd = 2 * x + N2
Q = 7 * x**2 + (x + 2 * y) ** 2
Qd = sp.expand(sp.diff(Q, x) * xd + sp.diff(Q, y) * yd)
print("Qdot + Q =", sp.factor(Qdot_plus := sp.expand(Qd + Q)))
sub = {x: p / sp.sqrt(7), y: (q - p / sp.sqrt(7)) / 2}
pd = sp.expand((sp.sqrt(7) * xd).subs(sub))
qd = sp.expand((xd + 2 * yd).subs(sub))
print("p' =", pd)
print("q' =", qd)
lin_p = sp.expand(-p / 2 - sp.sqrt(7) / 2 * q)
lin_q = sp.expand(sp.sqrt(7) / 2 * p - q / 2)
print("linear part p' check:", sp.simplify(pd - lin_p - (pd - lin_p)), " nonlinear p:", sp.simplify(pd - lin_p))
print("nonlinear q:", sp.simplify(qd - lin_q))
# Jacobian at (1,2) and eigenvalues
u, v = sp.symbols("u v")
J = sp.Matrix([u * (3 - u - v), v * (u - 1)]).jacobian([u, v]).subs({u: 1, v: 2})
print("J =", J, " eigenvalues:", J.eigenvals())
# at y = 0
print("Q at y=0:", sp.expand(Q.subs(y, 0)), "; lambda-2 at y=0:", sp.expand((1 + x) * 2 - 2))
# cubic error coefficients on the unit circle p = cos th, q = sin th
unit = {p: sp.cos(th), q: sp.sin(th)}
c1 = sp.simplify(Qdot_plus.subs(sub).subs(unit))           # dlogQ/dt = -1 + r*c1
c2 = sp.simplify((p * (qd - lin_q) - q * (pd - lin_p)).subs(unit))  # theta' = sqrt7/2 + r*c2
f1 = sp.lambdify(th, c1, "mpmath")
f2 = sp.lambdify(th, c2, "mpmath")
mp.mp.dps = 20
grid = [2 * mp.pi * i / 200000 for i in range(200000)]
m1 = max(abs(f1(t)) for t in grid)
m2 = max(abs(f2(t)) for t in grid)
print("sup|c1| (dlogQ/dt + 1)/sqrtQ  ~", mp.nstr(m1, 10))
print("sup|c2| (theta' - sqrt7/2)/sqrtQ ~", mp.nstr(m2, 10))
# crude bounds: |x| <= r/sqrt7, |y| <= r*sqrt(2/7)
print("crude |x|<=r/sqrt7 =", mp.nstr(1 / mp.sqrt(7), 8), " |y|<=r*sqrt(2/7) =", mp.nstr(mp.sqrt(mp.mpf(2) / 7), 8))
# half-turn average of the first-order corrections (predicts the 0.04976 constant to leading order?)
