import sympy as sp
a,O,w0,wa=sp.symbols('a Omega w0 wa')
# flat matter + CPL: E^2(a)
E2=O*a**-3+(1-O)*a**(-3*(1+w0+wa))*sp.exp(-3*wa*(1-a))
H=sp.sqrt(E2)
# derivatives: d/dt = a H d/da ; coefficients a^(n)/(a H^n) at a=1 (H0=1)
f=a; vals=[]
for n in range(1,6):
    f=a*H*sp.diff(f,a)
    vals.append(sp.simplify((f/(a*H**n)).subs(a,1)))
q=-vals[1]; j=vals[2]; s=vals[3]; l=vals[4]
q,j,s,l=[sp.expand(sp.simplify(x)) for x in (q,j,s,l)]
printed_l=sp.Rational(35,2)+(1-O)/4*(213+(7-O)*wa)*wa+(1-O)/4*(489+9*(82-21*O)*wa)*w0+sp.Rational(9,2)*(1-O)*(67-21*O+sp.Rational(3,2)*(23-11*O)*wa)*w0**2+sp.Rational(27,4)*(1-O)*(47-24*O)*w0**3+sp.Rational(81,2)*(1-O)*(3-2*O)*w0**4
print('q',sp.factor(q-(sp.Rational(1,2)+sp.Rational(3,2)*(1-O)*w0)))
print('j',sp.factor(j-(1+sp.Rational(3,2)*(1-O)*(3*w0*(1+w0)+wa))))
print('l printed - true:',sp.factor(sp.expand(printed_l-l)))
print('LCDM check l at w0=-1,wa=0:',sp.factor(l.subs({w0:-1,wa:0})))
