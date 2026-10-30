# V for Work/Cosmography/CVdQ.lean: seriesY(correct)(y) * T(y) - seriesQ(correct)(y) = y^4 V(y)
import sympy as sp
q,j,y=sp.symbols('q j y')
S=y*(1+(-sp.Rational(1,2))*(-3+q)*y+sp.Rational(1,6)*(12-5*q+3*q**2-j-1)*y**2)
T=1-sp.Rational(3,2)*y+sp.Rational(3,8)*y**2
SQ=y*(1-q/2*y+sp.Rational(1,24)*(3-2*q+12*q**2-4*(j+1))*y**2)
d=sp.expand(S*T-SQ)
assert all(d.coeff(y,k)==0 for k in range(4))
print(str(sp.expand(d/y**4)).replace('**','^'))
# check vs exact (1-y)^(3/2)
print(sp.series((1-y)**sp.Rational(3,2),y,0,3))
