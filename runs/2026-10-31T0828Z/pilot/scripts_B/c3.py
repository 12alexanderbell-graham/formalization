from sympy import *
Om=Rational(3,10)
q=Rational(3,2)*Om-1; j=1; s=1-Rational(9,2)*Om; l=1+3*Om+Rational(27,2)*Om**2
def D4(c):
    return 1+2*q+3*q**2+Rational(5,2)*q**3+c*q**4-Rational(5,3)*q*j-Rational(7,8)*q**2*j-j+Rational(1,12)*j**2-Rational(1,8)*q*s-s/6-l/120
print(q,float(D4(Rational(7,8))),float(D4(Rational(7,2))),float(D4(Rational(7,2))-D4(Rational(7,8))), float(Rational(21,8)*q**4))
print(l, float(l))
# eta
O=symbols('Omega')
c20=lambda O: -2*(27*O**2+24*O-32)/(27*O*(O-2)*(27*O**2+60*O+112))
c30=lambda O: -2*(81*O**2-60*O-16)/(243*O**2*(O-2)*(27*O**2+60*O+112))
for o in [Rational(41,1000),Rational(1,4)]:
    print(o,float(c20(o)),float(c30(o)))
print([N(r,8) for r in solve(54*O**2-29*O-2,O)],[N(r,8) for r in solve(27*O**2+24*O-32,O)])
