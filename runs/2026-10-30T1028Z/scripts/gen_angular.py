# C7: d_A = d_L (1-y)^2. Checks printed D_{A,y} against the corrected D_{L,y} and emits V with (1-y)^2 S_L(y) = S_A(y) + y^6 V(y).
import sympy as sp
q,j,s,l,O,y=sp.symbols('q j s l Omega y')
D1=-sp.Rational(1,2)*(-3+q); D2=sp.Rational(1,6)*(12-5*q+3*q**2-j-O)
pD3=sp.Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*O*(1+3*q))
pD4=sp.Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*O*(17-6*q+9*q**2-2*j))
D3=pD3+(O-1)*(3*q-2)/6; D4=pD4+(O-1)**2/120+5*q*(O-1)/12
SL=y*(1+D1*y+D2*y**2+D3*y**3+D4*y**4)
A1=-sp.Rational(1,2)*(1+q); A2=-sp.Rational(1,6)*(-q-3*q**2+j+O)
pA3=-sp.Rational(1,24)*(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*O)
pA4=-sp.Rational(1,120)*(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*O)
prod=sp.expand((1-y)**2*SL)
c=[prod.coeff(y,i) for i in range(7)]
print('A0', sp.simplify(c[1]-1), 'A1', sp.simplify(c[2]-A1), 'A2', sp.simplify(c[3]-A2))
print('pA3-A3', sp.factor(pA3-c[4])); print('pA4-A4', sp.factor(pA4-c[5]))
cA3=sp.expand(pA3-(pA3-c[4])); cA4=sp.expand(pA4-(pA4-c[5]))
SA=y*(1+A1*y+A2*y**2+c[4]*y**3+c[5]*y**4)
V=sp.expand((prod-sp.expand(SA))/y**6); assert sp.expand(prod-SA-y**6*V)==0
print('corr3', sp.factor(c[4]-pA3)); print('corr4', sp.factor(c[5]-pA4))
print('V :=', str(V).replace('**','^'))
