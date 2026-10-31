from sympy import *
O,e=symbols('Omega epsilon')
def P0(q,j,s,l): return (j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
def Q0(q,j,s,l): return (q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
def P2(q,j,s): return 9*s+6*j+9*q**2+66*q+42
def Q2(q,j,s): return -(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
def P3(q,j,s,l): return 3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
def Q3(q,j,s,l): return -(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
def Rp(q,j,s,l): return (j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
qL=Rational(3,2)*O-1; jL=1; sL=1-Rational(9,2)*O; lL=1+3*O+Rational(27,2)*O**2
f=1+e
q,j,s,l=qL*f,jL*f,sL*f,lL*f
eta20=(P2(q,j,s)*O+Q2(q,j,s))/(36*(P0(q,j,s,l)*O+Q0(q,j,s,l)))
eta30=(P3(q,j,s,l)*O+Q3(q,j,s,l))/(216*(j-q-2)*(P0(q,j,s,l)*O+Q0(q,j,s,l)))
print('eta20(0)',simplify(eta20.subs(e,0)),'eta30(0)',simplify(eta30.subs(e,0)))
d20=simplify(diff(eta20,e).subs(e,0)); d30=simplify(diff(eta30,e).subs(e,0))
c20=-2*(27*O**2+24*O-32)/(27*O*(O-2)*(27*O**2+60*O+112))
c30=-2*(81*O**2-60*O-16)/(243*O**2*(O-2)*(27*O**2+60*O+112))
print(simplify(d20-c20),simplify(d30-c30))
print(factor(d20),factor(d30))
den=(3*(9*O+74)*O-556)*O**2+16
p20=(64-6*O*(9*O+8))/den/27
p30=(6*((81*O-110)*O+40)*O+16)/den/(243*O**2)
print(factor(den))
print('P0Om+Q0 at LCDM',factor(simplify(P0(qL,1,sL,lL)*O+Q0(qL,1,sL,lL))))
print('printedR at LCDM',factor(simplify(Rp(qL,1,sL,lL))), expand(simplify(Rp(qL,1,sL,lL))))
print(factor(simplify(p20-c20)),'\n',factor(simplify(p30-c30)))
