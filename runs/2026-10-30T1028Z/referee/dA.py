import sympy as sp
q,j,s,l,Om,y=sp.symbols('q j s l Omega0 y')
DL=[1, sp.Rational(3,2)-q/2, -Om/6 - j/6 + q**2/2 - 5*q/6 + 2,
 Om*q/4 - 5*Om/12 + 5*j*q/12 - 7*j/24 - 5*q**3/8 + 7*q**2/8 - 4*q/3 + s/24 + sp.Rational(5,2),
 Om**2/120 + Om*j/12 - 3*Om*q**2/8 + 2*Om*q/3 - 29*Om/40 + j**2/12 - 7*j*q**2/8 + 3*j*q/4 - 19*j/40 - l/120 + 7*q**4/8 - 9*q**3/8 + 31*q**2/20 - q*s/8 - 39*q/20 + 3*s/40 + 3]
PL=[1, -sp.Rational(1,2)*(-3+q), -sp.Rational(1,6)*(12-5*q+3*q**2-j-Om),
 sp.Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q)),
 sp.Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j))]
PA=[1, -sp.Rational(1,2)*(1+q), -sp.Rational(1,6)*(-q-3*q**2+j+Om),
 -sp.Rational(1,24)*(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*Om),
 -sp.Rational(1,120)*(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*Om)]
def toA(D):
    ser=sp.expand(sum(D[n]*y**(n+1) for n in range(5))*(1-y)**2)
    return [sp.expand(ser.coeff(y,n+1)) for n in range(5)]
DA=toA(DL)
for n in range(5): print('DA%d printed-correct:'%n, sp.factor(sp.expand(PA[n]-DA[n])))
# is printed d_A consistent with printed d_L (with or without D2 sign fix)?
PLA=toA(PL)
for n in range(5): print('  printed dA - (printed dL)(1-y)^2, n=%d:'%n, sp.factor(sp.expand(PA[n]-PLA[n])))
PLfix=PL[:]; PLfix[2]=-PL[2]
PLA2=toA(PLfix)
for n in range(5): print('  printed dA - (printed dL with D2 fixed)(1-y)^2, n=%d:'%n, sp.factor(sp.expand(PA[n]-PLA2[n])))
