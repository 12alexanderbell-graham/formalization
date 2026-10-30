"""Dunsby & Luongo, arXiv:1511.06532 (IJGMMP 13 (2016) 1630002). Transcribed via WebFetch of arxiv.org/pdf.
Flat (Omega_k = 0) d_L series Eq.(13)-(14) incl. alpha_5 with maxout m0 (6th derivative); Eq.(8),(11),(60)."""
from common import *
import sympy as sp
R=sp.Rational
m,T,Tp,t=sp.symbols('m T Tp t')
# 6th-order flat reference for d_L (coefficient-list series arithmetic)
from pseries import PS
NN=7
a = PS([1,-1,-q/2,-j/6,s/24,-l/120,m/720],NN)      # a(t0 - T/H0)
inva = a.inv()
zT = inva - 1
Tz = zT.revert()
chi = inva.integ().compose(Tz)
dL6 = (PS([1,1],NN)*chi).expr(z)
print('flat dL z^6 ref:', sp.factor(dL6.coeff(z,6)))
al = [1, R(1,2)-q/2, -R(1,6)-j/6+q/6+q**2/2,
      R(1,12)+R(5,24)*j-q/12+R(5,12)*j*q-R(5,8)*q**2-R(5,8)*q**3+s/24,
      -R(1,20)-R(9,40)*j+j**2/12-l/120+q/20-R(11,12)*j*q+R(27,40)*q**2-R(7,8)*j*q**2+R(11,8)*q**3+R(7,8)*q**4-R(11,120)*s-q*s/8,
      R(1,30)+R(7,30)*j-R(19,72)*j**2+R(19,720)*l+m/720-q/30+R(13,9)*j*q-R(7,18)*j**2*q+R(7,240)*l*q-R(7,10)*q**2
      +R(133,48)*j*q**2-R(13,6)*q**3+R(7,4)*j*q**3-R(133,48)*q**4-R(21,16)*q**5+R(13,90)*s-R(7,144)*j*s+R(19,48)*q*s+R(7,24)*q**2*s]
dLp = sum(al[n]*z**(n+1) for n in range(6))
compare('DL2016 eq13-14 dL(z) flat', dLp, dL6, z, 6)
# Eq.(60) D(z)
D60 = z*(1-(1+q/2)*z+(1+q+q**2/2-j/6)*z**2-(1+R(3,2)*q*(1+q)+R(5,8)*q**3-j/2-R(5,12)*q*j-s/24)*z**3)
compare('DL2016 eq60 D(z)', D60, REF['lookback'], z, 4)
# Eq.(11) time derivatives of H, and Eq.(8): use generic A(t)
A=sp.Function('A')(t); Hf=A.diff(t)/A
qf=-A.diff(t,2)/A/Hf**2; jf=A.diff(t,3)/A/Hf**3; sf=A.diff(t,4)/A/Hf**4; lf=A.diff(t,5)/A/Hf**5; mf=A.diff(t,6)/A/Hf**6
chk = {
 '11a': (Hf.diff(t), -Hf**2*(1+qf)),
 '11b': (Hf.diff(t,2), Hf**3*(jf+3*qf+2)),
 '11c': (Hf.diff(t,3), Hf**4*(sf-4*jf-3*qf*(qf+4)-6)),
 '11d': (Hf.diff(t,4), Hf**5*(lf-5*sf+10*(qf+2)*jf+30*(qf+2)*qf+24)),
 '11e': (Hf.diff(t,5), Hf**6*(mf-10*jf**2-120*jf*(qf+1)-3*(2*lf+5*(24*qf+18*qf**2+2*qf**3-2*sf-qf*sf+8)))),
 '8a': (qf.diff(t), -Hf*(jf-2*qf**2-qf)),
 '8b': (jf.diff(t), Hf*(sf+jf*(2+3*qf))),
 '8c': (sf.diff(t), Hf*(lf+sf*(3+4*qf))),
 '8d': (lf.diff(t), Hf*(mf+lf*(4+5*qf))),
}
for k_,(lhs,rhs) in chk.items():
    d=sp.simplify(lhs-rhs)
    print(('OK   ' if d==0 else 'DIFF ')+'DL2016 eq'+k_, '' if d==0 else sp.factor(sp.simplify(d/Hf**6)))
