from sympy import *
Om=symbols('Omega')
def P0(q,j,s,l): return (j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
def Q0(q,j,s,l): return (q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
def P2(q,j,s): return 9*s+6*j+9*q**2+66*q+42
def Q2(q,j,s): return -(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
def P3(q,j,s,l): return 3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
def Q3(q,j,s,l): return -(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
def printedR(q,j,s,l): return (j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
qL=Rational(3,2)*Om-1; jL=1; sL=1-Rational(9,2)*Om; lL=1+3*Om+Rational(27,2)*Om**2
N0=P0(qL,jL,sL,lL)*Om+Q0(qL,jL,sL,lL)
R=printedR(qL,jL,sL,lL)
