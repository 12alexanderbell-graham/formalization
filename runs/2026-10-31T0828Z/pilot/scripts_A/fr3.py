from sympy import *
from fr import P0,Q0,P2,Q2,P3,Q3,printedR
t,q,j,s,l,Om,F0,F2,F3=symbols('t q j s l Omega F0 F2 F3')
a=1+t-q*t**2/2+j*t**3/6+s*t**4/24+l*t**5/120
H=diff(a,t)/a
Hs=series(H,t,0,5).removeO()   # H(t)
R=-6*(diff(Hs,t)+2*Hs**2)
R=expand(R)
R0=R.subs(t,0)
dR=diff(R,t); ddR=diff(R,t,2)
x=R-R0
Fp=1+F2*x+F3*x**2/2        # F'
Fpp=F2+F3*x                # F''
Fppp=F3                    # F'''
Ft=F0+x+F2*x**2/2+F3*x**3/6
rho=3*Om*a**-3
Hd=diff(Hs,t)
master=-2*Fp*Hd-(rho+ddR*Fpp+dR*(dR*Fppp-Hs*Fpp))
fried=3*Fp*Hs**2-(rho+(Ft-R*Fp)/2-3*Hs*dR*Fpp)
eqs=[fried.subs(t,0), master.subs(t,0), diff(master,t).subs(t,0)]
sol=solve(eqs,[F0,F2,F3],dict=True)[0]
F0s=simplify(sol[F0]); F2s=simplify(sol[F2]); F3s=simplify(sol[F3])
Rc=printedR(q,j,s,l)
print(simplify(F0s*Rc+6*(P0(q,j,s,l)*Om+Q0(q,j,s,l))))
print(simplify(F2s*Rc*(-6)/(-6)))
print(simplify(F2s/F0s - (P2(q,j,s)*Om+Q2(q,j,s))/(P0(q,j,s,l)*Om+Q0(q,j,s,l))*Rational(1,1)))
print(simplify(F3s/F0s))
import pickle; pickle.dump((F0s,F2s,F3s,R0),open('fsol.pkl','wb'))
