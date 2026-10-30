"""Capozziello, Cardone, Salzano, arXiv:0802.1583 (PRD 78 (2008) 063504), Appendix A.
Transcribed via WebFetch of arxiv.org/pdf and web3.arxiv.org/pdf (term-by-term listings).
Convention: K = k c^2/(H0^2 a0^2) = -Omega_k ; D = c*(t0-t) ; r0 is comoving coordinate (a0 r0 = S_k(chi) a0)."""
from common import *
import sympy as sp
R=sp.Rational; K=-Ok
T,Tp=sp.symbols('T Tp')
P={}
# (A2) D(z) = (c z/H0){...}
Dz = z*(1 - (1+q/2)*z + (1+q+q**2/2-j/6)*z**2
        - (1+R(3,2)*q+R(3,2)*q**2+R(5,8)*q**3-j/2-R(5,12)*q*j-s/24)*z**3
        + (1+2*q+3*q**2+R(5,2)*q**3+R(7,2)*q**4-R(5,3)*q*j-R(7,8)*q**2*j-j+j**2/12-q*s/8-s/6-l/120)*z**4)
P['A2 D(z)=c*lookback'] = (Dz, REF['lookback'], z, 5)
# (A6) dL(z)
dL = (z - R(1,2)*(-1+q)*z**2 - R(1,6)*(1-q-3*q**2+j+K)*z**3
      + (R(1,24)*(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s) + 2*K*(1+3*q)/24)*z**4
      + (R(1,120)*(-6+6*q+81*q**2+165*q**3+105*q**4) + R(1,120)*(10*j**2-27*j-110*q*j-105*q**2*j)
         - R(1,120)*(15*q*s+11*s+l) - 5*K*(1+8*q+9*q**2-2*j)/120)*z**5)
P['A6 dL(z)'] = (dL, REF['dL'], z, 5)
dA = (z - R(1,2)*(3+q)*z**2 + R(1,6)*(11+7*q+3*q**2-j-K)*z**3
      + (-R(1,24)*(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s) + 2*K*(5+3*q)/24)*z**4
      + (R(1,120)*(274+326*q+411*q**2+315*q**3+105*q**4) + R(1,120)*(10*j**2-137*j-210*q*j-105*q**2*j-15*q*s-21*s-l)
         - 5*K*(17+20*q+9*q**2-2*j)/120)*z**5)
P['A7 dA(z)'] = (dA, REF['dA'], z, 5)
# reference r(D): D = T in units c/H0
a = 1 - T - q/2*T**2 - j/6*T**3 + s/24*T**4 - l/120*T**5
chiT = sp.integrate(ser(1/a.subs(T,Tp),Tp,6),(Tp,0,T))
rT = ser(chiT + Ok*chiT**3/6 + Ok**2*chiT**5/120, T, 7)
refRD = ser(rT/T, T, 6)
RD = (1 + T/2 + R(1,6)*(2+q-K)*T**2 + R(1,24)*(6+6*q+j-6*K)*T**3
      + (R(1,120)*(24+36*q+6*q**2+8*j-s) - 5*K*(7+2*q)/120)*T**4
      + (R(1,144)*(24+48*q+18*q**2+4*q*j+12*j-2*s+24*l) - 3*K*(15+10*q+j)/144)*T**5)
P['A5 r0(D)/(D/a0)'] = (RD, refRD, T, 5)
if __name__=='__main__':
    for k_,(pr,rf,v,n) in P.items(): compare('CCS2008 '+k_, pr, rf, v, n)
    print('reference r/D coefficients:'); [print('  T^%d'%i, sp.factor(refRD.coeff(T,i))) for i in range(6)]
