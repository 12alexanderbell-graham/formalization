from sympy import *
z,Om,w0,wa=symbols('z Omega w0 wa')
E=sqrt(Om*(1+z)**3+(1-Om)*(1+z)**(3*(1+w0+wa))*exp(-3*wa*z/(1+z)))
a=1/(1+z)
f=a
for i in range(5): f=-(1+z)*E*diff(f,z)
l=simplify((f/(a*E**5)).subs(z,0))
l=expand(simplify(l))
print(l)
printed=Rational(35,2)+(1-Om)/4*(213+(7-Om)*wa)*wa+(1-Om)/4*(489+9*(82-21*Om)*wa)*w0+Rational(9,2)*(1-Om)*(67-21*Om+Rational(3,2)*(23-11*Om)*wa)*w0**2+Rational(27,4)*(1-Om)*(47-24*Om)*w0**3+Rational(81,2)*(1-Om)*(3-2*Om)*w0**4
d=factor(expand(printed-l))
print(d)
printed2=printed.subs(wa,wa)  
# with wa^2 term x9
corr=printed+ (1-Om)/4*(7-Om)*wa**2*8
print(simplify(expand(corr-l)))
