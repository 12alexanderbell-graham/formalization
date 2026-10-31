from sympy import *
O=symbols('Omega')
def R(q,j,s,l,c): return (j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+c)*j-(3*q**4+34*q**3+246*q+104)
qL=Rational(3,2)*O-1; sL=1-Rational(9,2)*O; lL=1+3*O+Rational(27,2)*O**2
for c in [18,-18]:
    print(c, expand(R(qL,1,sL,lL,c)))
print(expand(-9*O**2*(27*O**2+60*O+112)/16))
