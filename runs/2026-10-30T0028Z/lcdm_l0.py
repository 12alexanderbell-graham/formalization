import sympy as sp
a,Om=sp.symbols('a Omega_m',positive=True)
adot = a*sp.sqrt(Om/a**3 + 1-Om)   # H0=1
D=lambda f: sp.diff(f,a)*adot     # d/dt
ders=[a]; 
for n in range(5): ders.append(sp.simplify(D(ders[-1])))
at1=[sp.simplify(d.subs(a,1)) for d in ders]
ad=at1[1]
q=sp.simplify(-at1[2]/ad**2); j=sp.simplify(at1[3]/ad**3); s=sp.simplify(at1[4]/ad**4); l=sp.simplify(at1[5]/ad**5)
print("q0",sp.expand(q)); print("j0",sp.expand(j)); print("s0",sp.expand(s)); print("l0",sp.expand(l))
print("EdS l0", l.subs(Om,1), " printed AGLQ l0 at Om=1:", (1+3*Om-sp.Rational(27,2)*Om**2).subs(Om,1))
