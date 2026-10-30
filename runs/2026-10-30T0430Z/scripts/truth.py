# Independent route: d/dt = a H d/da with E^2(a) (a0=1,H0=1); coefficients a^(n)/(a H^n) at a=1.
import sympy as sp
a,O,w0,wa=sp.symbols('a Omega w0 wa')
E2=O*a**-3+(1-O)*a**(-3*(1+w0+wa))*sp.exp(-3*wa*(1-a))
H=sp.sqrt(E2)
f=a; vals=[]
for n in range(1,6):
    f=a*H*sp.diff(f,a)
    vals.append(sp.expand(sp.simplify((f/(a*H**n)).subs(a,1))))
q=-vals[1]; j,s,l=vals[2],vals[3],vals[4]
for nm,v in (('q',q),('j',j),('s',s),('l',l)): print(nm,'=',sp.factor(v)); print('   expanded:',v)
printed_l=sp.Rational(35,2)+(1-O)/4*(213+(7-O)*wa)*wa+(1-O)/4*(489+9*(82-21*O)*wa)*w0+sp.Rational(9,2)*(1-O)*(67-21*O+sp.Rational(3,2)*(23-11*O)*wa)*w0**2+sp.Rational(27,4)*(1-O)*(47-24*O)*w0**3+sp.Rational(81,2)*(1-O)*(3-2*O)*w0**4
print('printed-true l:',sp.factor(sp.expand(printed_l-l)))
printed_s=-sp.Rational(7,2)-sp.Rational(33,4)*(1-O)*wa-sp.Rational(9,4)*(1-O)*(9+(7-O)*wa)*w0-sp.Rational(9,4)*(1-O)*(16-3*O)*w0**2-sp.Rational(27,4)*(1-O)*(3-O)*w0**3
print('printed(with - restored)-true s:',sp.factor(sp.expand(printed_s-s)))
print('witness O=0,w0=-1,wa=2/3: true l=',l.subs({O:0,w0:-1,wa:sp.Rational(2,3)}),' printed=',printed_l.subs({O:0,w0:-1,wa:sp.Rational(2,3)}))
