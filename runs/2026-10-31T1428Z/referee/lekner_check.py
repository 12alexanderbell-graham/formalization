"""Referee: Lekner (1982) parametric vdW coexistence, as printed in Johnston arXiv:1402.1205 eqs. (78)-(79).
1. Transcription check: reproduce Johnston's printed Table VI row y = 1 and Table IV row T/Tc = 0.70.
2. Symbolic check (sympy, E = e^y): P_r(V_l) = P_r(V_g) = p_X and the Maxwell equal-area identity, where the
   log in the antiderivative collapses to log((3V_g-1)/(3V_l-1)) = 2y.
3. Solve tau_X(y) = 0.7 at high precision and compare p_X with the interval result of certify_vdw.py.
Reduced vdW: P_r = 8 tau/(3V - 1) - 3/V^2 (V = v/v_c = x/3).
"""
import mpmath as m
import sympy as sp
m.mp.dps = 50

def lek(y):
    f = (y*m.cosh(y) - m.sinh(y)) / (m.sinh(y)*m.cosh(y) - y)
    g = 1 + 2*f*m.cosh(y) + f**2
    tau = 27*f*(f + m.cosh(y)) / (4*g**2)
    p = 27*f**2*(1 - f**2) / g**2
    Vg = (1 + m.e**y/f)/3
    Vl = (1 + m.e**(-y)/f)/3
    return tau, p, Vl, Vg

t, p, Vl, Vg = lek(m.mpf(1))
print("y=1: tau=%s p=%s dV=%s n_g=%s n_l=%s" % tuple(m.nstr(z, 6) for z in (t, p, Vg - Vl, 1/Vg, 1/Vl)))
print("      printed (Johnston Table VI): 0.90088 6.4971e-01 1.7324e+00 4.2793e-01 1.6543")
y7 = m.findroot(lambda y: lek(y)[0] - m.mpf('0.7'), 2.0)
t, p, Vl, Vg = lek(y7)
print("tau=0.7: y=%s p=%s V_l=%s V_g=%s" % tuple(m.nstr(z, 22) for z in (y7, p, Vl, Vg)))
print("      printed (Johnston Table IV, T/Tc=0.70): pX/pc 2.005e-01, V_G/Vc 0.4672, V_C/Vc 7.811")
P = lambda V: 8*t/(3*V - 1) - 3/V**2
print("check P(V_l)-p, P(V_g)-p:", m.nstr(P(Vl) - p, 5), m.nstr(P(Vg) - p, 5))
A = (8*t/3)*m.log((3*Vg - 1)/(3*Vl - 1)) + 3/Vg - 3/Vl     # = int_{Vl}^{Vg} P_r dV, antiderivative (8t/3)log(3V-1)+3/V
print("equal area residual:", m.nstr(A - p*(Vg - Vl), 5))
print("omega = -log10(p) - 1 =", m.nstr(-m.log10(p) - 1, 22))

# symbolic identities in E = e^y (y = log E): f, cosh, sinh rational in E, y kept as symbol
E, y = sp.symbols('E y', positive=True)
ch, sh = (E + 1/E)/2, (E - 1/E)/2
f = (y*ch - sh)/(sh*ch - y)
g = 1 + 2*f*ch + f**2
tau = 27*f*(f + ch)/(4*g**2)
pX = 27*f**2*(1 - f**2)/g**2
Vg_, Vl_ = (1 + E/f)/3, (1 + 1/(E*f))/3
Pr = lambda V: 8*tau/(3*V - 1) - 3/V**2
print("sympy P(V_l) - p  ==0:", sp.simplify(sp.together(Pr(Vl_) - pX)) == 0)
print("sympy P(V_g) - p  ==0:", sp.simplify(sp.together(Pr(Vg_) - pX)) == 0)
# (3Vg-1)/(3Vl-1) = E^2 exactly, so log term = (8 tau/3)*2y
print("sympy (3Vg-1)/(3Vl-1) == E^2:", sp.simplify((3*Vg_ - 1)/(3*Vl_ - 1) - E**2) == 0)
area = (8*tau/3)*2*y + 3/Vg_ - 3/Vl_ - pX*(Vg_ - Vl_)
print("sympy equal-area identity ==0:", sp.simplify(sp.together(area)) == 0)
