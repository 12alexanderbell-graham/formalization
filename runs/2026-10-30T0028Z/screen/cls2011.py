"""Capozziello, Lazkoz, Salzano, arXiv:1104.3096 (PRD 84 (2011) 124061). Transcribed via WebFetch (ar5iv + arxiv pdf, term lists).
Flat. Eq.(4) mu(z) coefficients M1..M4; Eqs.(12)-(15) z-derivatives of H as identities in z; Eqs.(19)-(22) CPL values."""
from common import *
R=sp.Rational; fl={Ok:0}
M = (-R(1,2)*(-1+q)*z - R(1,24)*(7-10*q-9*q**2+4*j)*z**2 + R(1,24)*(5-9*q-16*q**2-10*q**3+7*j+8*q*j+s)*z**3
     + R(1,2880)*(-469+1004*q+2654*q**2+3300*q**3+1575*q**4+200*j**2-1148*j-2620*q*j-1800*q**2*j-300*q*s-324*s-24*l)*z**4)
compare('CLS2011 eq4 mu(z): ln(dL/z) coefficients', M, REF['lnDLoverZ'].subs(fl), z, 4)
# Eqs (12)-(15) as identities valid at all z: use generic a(t); 1+z=a0/a ; d/dz = -(1/((1+z)H)) d/dt
t=sp.symbols('t'); A=sp.Function('A')(t); Hf=A.diff(t)/A; zp1=1/A
qf=-A.diff(t,2)/A/Hf**2; jf=A.diff(t,3)/A/Hf**3; sf=A.diff(t,4)/A/Hf**4; lf=A.diff(t,5)/A/Hf**5
Dz=lambda e: -e.diff(t)/(zp1*Hf)
d1=Dz(Hf); d2=Dz(d1); d3=Dz(d2); d4=Dz(d3)
chk={'12':(d1,Hf*(1+qf)/zp1),'13':(d2,Hf*(jf-qf**2)/zp1**2),'14':(d3,Hf*(3*qf**2+3*qf**3-4*qf*jf-3*jf-sf)/zp1**3),
     '15':(d4,Hf*(-12*qf**2-24*qf**3-15*qf**4+32*qf*jf+25*qf**2*jf+7*qf*sf+12*jf-4*jf**2+8*sf+lf)/zp1**4)}
for k_,(a_,b_) in chk.items():
    d=sp.simplify(a_-b_); print(('OK   ' if d==0 else 'DIFF ')+'CLS2011 eq'+k_+' d^nH/dz^n identity (all z)')
# CPL values: flat, H^2 = Om(1+z)^3 + (1-Om)(1+z)^(3(1+w0+wa)) exp(-3 wa z/(1+z))
Om,w0,wa=sp.symbols('Omega_m w0 wa')
E=sp.sqrt(Om*(1+z)**3+(1-Om)*(1+z)**(3*(1+w0+wa))*sp.exp(-3*wa*z/(1+z)))
Es=ser(E,z,5)
# solve REF Hz coefficients for q,j,s,l
sol={}
for i,v in zip(range(1,5),(q,j,s,l)):
    eq=sp.expand(REF['Hz'].coeff(z,i).subs(sol)-Es.coeff(z,i)); sol[v]=sp.expand(sp.solve(eq,v)[0])
X=1-Om
pr={q: R(1,2)+R(3,2)*X*w0, j: 1+R(3,2)*X*(3*w0*(1+w0)+wa),
    s: -R(7,2)-R(33,4)*X*wa-R(9,4)*X*(9+(7-Om)*wa)*w0-R(9,4)*X*(16-3*Om)*w0**2+R(27,4)*X*(3-Om)*w0**3,
    l: R(35,2)+X/4*(213+(7-Om)*wa)*wa+X/4*(489+9*(82-21*Om)*wa)*w0+R(9,2)*X*(67-21*Om+R(3,2)*(23-11*Om)*wa)*w0**2
       +R(27,4)*X*(47-24*Om)*w0**3+R(81,2)*X*(3-2*Om)*w0**4}
for v in (q,j,s,l):
    d=sp.factor(sp.expand(pr[v]-sol[v]))
    print(('OK   ' if d==0 else 'DIFF ')+'CLS2011 CPL %s0'%v, '' if d==0 else '| printed-exact = %s'%d)
    if d!=0: print('     exact:', sp.collect(sol[v],[w0,wa]))
