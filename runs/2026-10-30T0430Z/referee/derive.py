import sympy as sp
z,Om,w0,wa=sp.symbols('z Omega_m w0 wa')
E2=Om*(1+z)**3+(1-Om)*(1+z)**(3*(1+w0+wa))*sp.exp(-3*wa*z/(1+z))
H=sp.sqrt(E2)
# f_n = a^(n)/a, a=1/(1+z), d/dt = -(1+z) H d/dz
f=[None,H]
for n in range(1,5):
    fn=f[n]
    f.append(sp.simplify(H*fn-(1+z)*H*sp.diff(fn,z)))
def at0(e): return sp.expand(sp.simplify(e.subs(z,0)))
q0=at0(-f[2]/H**2); j0=at0(f[3]/H**3); s0=at0(f[4]/H**4); l0=at0(f[5]/H**5)
print('q0',sp.factor(q0)); print('j0',sp.factor(j0))
Ob=1-Om
s0p=-sp.Rational(7,2)-sp.Rational(33,4)*Ob*wa-sp.Rational(9,4)*Ob*(9+(7-Om)*wa)*w0-sp.Rational(9,4)*Ob*(16-3*Om)*w0**2-sp.Rational(27,4)*Ob*(3-Om)*w0**3
print('s0 - printed(with minus):',sp.simplify(s0-s0p))
s0plus=s0p+2*sp.Rational(27,4)*Ob*(3-Om)*w0**3
print('s0 - printed(with plus):',sp.factor(sp.simplify(s0-s0plus)))
def L(c):
    return sp.Rational(35,2)+Ob/4*(213+c*(7-Om)*wa)*wa+Ob/4*(489+9*(82-21*Om)*wa)*w0+sp.Rational(9,2)*Ob*(67-21*Om+sp.Rational(3,2)*(23-11*Om)*wa)*w0**2+sp.Rational(27,4)*Ob*(47-24*Om)*w0**3+sp.Rational(81,2)*Ob*(3-2*Om)*w0**4
print('l0 - printed:',sp.factor(sp.simplify(l0-L(1))))
print('l0 - corrected(9):',sp.simplify(l0-L(9)))
print('l0 coeff of wa^2:',sp.factor(sp.Poly(l0,wa,w0).coeff_monomial(wa**2)))
print('l0 =',sp.collect(l0,[w0,wa]))
# Om=0 witness
print('printed at Om=0,w0=-1,wa=2/3:',L(1).subs({Om:0,w0:-1,wa:sp.Rational(2,3)}),' true:',l0.subs({Om:0,w0:-1,wa:sp.Rational(2,3)}))
