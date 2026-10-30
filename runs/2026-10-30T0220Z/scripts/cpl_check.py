"""C4: Capozziello-Lazkoz-Salzano arXiv:1104.3096 Eqs.(19)-(22), flat matter + CPL DE.
E^2(a) = Om a^-3 + (1-Om) a^{-3(1+w0+wa)} exp(-3 wa (1-a))   [Eq.17 with 1+z=1/a, z/(1+z)=1-a]
q = -a''/(a H^2), j = a'''/(a H^3), s = a''''/(a H^4), l = a^(5)/(a H^5)   [Eq.2]
"""
import sympy as sp

a, Om, w0, wa = sp.symbols('a Omega_m w0 wa')
H = sp.sqrt(Om*a**-3 + (1-Om)*a**(-3*(1+w0+wa))*sp.exp(-3*wa*(1-a)))
f = [a]
for n in range(5):
    f.append(sp.simplify(a*H*sp.diff(f[-1], a)))   # d/dt = a H d/da
vals = [sp.simplify((f[n]/(a*H**n)).subs(a, 1)) for n in range(6)]
q0 = sp.expand(-vals[2]); j0 = sp.expand(vals[3]); s0 = sp.expand(vals[4]); l0 = sp.expand(vals[5])
R = sp.Rational
pq0 = R(1,2) + R(3,2)*(1-Om)*w0
pj0 = 1 + R(3,2)*(1-Om)*(3*w0*(1+w0) + wa)
# s0 as printed (with the missing operator between w0^2 and 27/4 taken as '+'):
ps0 = (-R(7,2) - R(33,4)*(1-Om)*wa - R(9,4)*(1-Om)*(9 + (7-Om)*wa)*w0
       - R(9,4)*(1-Om)*(16-3*Om)*w0**2 + R(27,4)*(1-Om)*(3-Om)*w0**3)
pl0 = (R(35,2) + (1-Om)/4*(213 + (7-Om)*wa)*wa
       + (1-Om)/4*(489 + 9*(82-21*Om)*wa)*w0
       + R(9,2)*(1-Om)*(67 - 21*Om + R(3,2)*(23-11*Om)*wa)*w0**2
       + R(27,4)*(1-Om)*(47-24*Om)*w0**3
       + R(81,2)*(1-Om)*(3-2*Om)*w0**4)
for name, d, p in [('q0', q0, pq0), ('j0', j0, pj0), ('s0', s0, ps0), ('l0', l0, pl0)]:
    print(f"{name} derived =", sp.collect(sp.expand(d), [w0, wa]))
    print(f"   printed - derived =", sp.factor(sp.expand(p - d)))
# show derived l0 grouped as in the paper
print("l0 derived, w0^0 part:", sp.factor(sp.expand(l0.subs(w0, 0) - R(35,2))))
print("l0 at w0=-1 printed-derived:", sp.factor(sp.expand((pl0 - l0).subs(w0, -1))))
