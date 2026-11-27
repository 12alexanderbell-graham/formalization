# Vacuum F(R) models with a Hubble rate linear in time (run 2026-11-27T1228Z, eta_ratios hypotheses 3, 4).
# Master equation of IsFRCosmo in time, phi(t) = F'(R(t)):  phi'' - H phi' + 2 H' phi + rho = 0.
# With rho = 0 and phi = 1 + b t + a t^2, H = k (2 a t + b), k = -2a/(4a - b^2) solves it exactly.
import sympy as sp
t,a,b=sp.symbols('t a b',real=True)
phi=1+b*t+a*t**2
k=-2*a/(4*a-b**2)
H=k*(2*a*t+b)
assert sp.simplify(sp.diff(phi,t,2)-H*sp.diff(phi,t)+2*sp.diff(H,t)*phi)==0
# scale factor a(t) = exp(int H), a(0)=1
A=sp.exp(sp.integrate(H,(t,0,t)))
H0=H.subs(t,0)
def coeff(n): return sp.simplify((sp.diff(A,t,n)/A/H**n).subs(t,0))
q=-coeff(2); j=coeff(3); s=coeff(4); l=coeff(5)
R=-6*(sp.diff(H,t)+2*H**2)
Rd=sp.diff(R,t)
# F derivatives along the curve: F'' = phi'/R', F''' = (F'')'/R', F'''' = (F''')'/R'
F2=sp.diff(phi,t)/Rd; F3=sp.diff(F2,t)/Rd; F4=sp.diff(F3,t)/Rd
print('q,j,s,l =',[sp.factor(x) for x in (q,j,s,l)])
def correctR(q,j,s,l):
    return (j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
cR=sp.factor(sp.simplify(correctR(q,j,s,l)))
print('correctR =',cR)
print('J =',sp.factor(j-q-2))
print('F4(R0) =',sp.factor(sp.simplify(F4.subs(t,0))))
