"""Cattoen & Visser, arXiv:0710.1887 (CQG 24 (2007) 5985). Transcribed via WebFetch of ar5iv HTML.
Convention: Omega_0 = 1 + k c^2/(H0^2 a0^2) = 1 - Omega_k ; d_H = c/H0."""
from common import *
R=sp.Rational
O0 = 1 - Ok
J = j + O0
P = {}
P['eq20 dL(z)'] = (z*(1 - R(1,2)*(-1+q)*z + R(1,6)*(q+3*q**2-J)*z**2), dist_family(0), z, 3)
P['eq21 dF(z)'] = (z*(1 - R(1,2)*q*z + R(1,24)*(3+10*q+12*q**2-4*J)*z**2), dist_family(1), z, 3)
P['eq22 dP(z)'] = (z*(1 - R(1,2)*(1+q)*z + R(1,6)*(3+4*q+3*q**2-J)*z**2), dist_family(2), z, 3)
P['eq23 dQ(z)'] = (z*(1 - R(1,2)*(2+q)*z + R(1,24)*(27+22*q+12*q**2-4*J)*z**2), dist_family(3), z, 3)
P['eq24 dA(z)'] = (z*(1 - R(1,2)*(3+q)*z + R(1,6)*(12+7*q+3*q**2-J)*z**2), dist_family(4), z, 3)
P['eq2 dL(z) k-form'] = (z*(1+R(1,2)*(1-q)*z - R(1,6)*(1-q-3*q**2+j-Ok)*z**2), dist_family(0), z, 3)
# log forms: ln(d/z) - ln dH
P['eq26 ln dL/z'] = (-R(1,2)*(-1+q)*z + R(1,24)*(-3+10*q+9*q**2-4*J)*z**2, lnfamily(0), z, 2)
P['eq25 mu (bracket)'] = (R(1,2)*(1-q)*z - R(1,24)*(3-10*q-9*q**2+4*J)*z**2, lnfamily(0), z, 2)
P['eq27 ln dF/z'] = (-R(1,2)*q*z + R(1,24)*(3+10*q+9*q**2-4*J)*z**2, lnfamily(1), z, 2)
P['eq28 ln dP/z'] = (-R(1,2)*(1+q)*z + R(1,24)*(9+10*q+9*q**2-4*J)*z**2, lnfamily(2), z, 2)
P['eq29 ln dQ/z'] = (-R(1,2)*(2+q)*z + R(1,24)*(15+10*q+9*q**2-4*J)*z**2, lnfamily(3), z, 2)
P['eq30 ln dA/z'] = (-R(1,2)*(3+q)*z + R(1,24)*(21+10*q+9*q**2-4*J)*z**2, lnfamily(4), z, 2)
P['eq52 dL(y)'] = (y*(1 - R(1,2)*(-3+q)*y + R(1,6)*(12-5*q+3*q**2-J)*y**2), dist_family(0,'y'), y, 3)
P['eq57 dF(y)'] = (y*(1 - R(1,2)*(-2+q)*y + R(1,24)*(27-14*q+12*q**2-4*J)*y**2), dist_family(1,'y'), y, 3)
P['eq58 dP(y)'] = (y*(1 - R(1,2)*(-1+q)*y + R(1,6)*(3-2*q+3*q**2-J)*y**2), dist_family(2,'y'), y, 3)
P['eq59 dQ(y)'] = (y*(1 - R(1,2)*q*y + R(1,12)*(3-2*q+12*q**2-4*J)*y**2), dist_family(3,'y'), y, 3)
P['eq60 dA(y)'] = (y*(1 - R(1,2)*(1+q)*y + R(1,6)*(q+3*q**2-J)*y**2), dist_family(4,'y'), y, 3)
P['eq61 ln dL/y'] = (-R(1,2)*(-3+q)*y + R(1,24)*(21-2*q+9*q**2-4*J)*y**2, lnfamily(0,'y'), y, 2)
P['eq62 ln dF/y'] = (-R(1,2)*(-2+q)*y + R(1,24)*(15-2*q+9*q**2-4*J)*y**2, lnfamily(1,'y'), y, 2)
P['eq63 ln dP/y'] = (-R(1,2)*(-1+q)*y + R(1,24)*(9-2*q+9*q**2-4*J)*y**2, lnfamily(2,'y'), y, 2)
P['eq64 ln dQ/y'] = (-R(1,2)*q*y + R(1,24)*(3-2*q+9*q**2-4*J)*y**2, lnfamily(3,'y'), y, 2)
P['eq65 ln dA/y'] = (-R(1,2)*(1+q)*y + R(1,24)*(-3-2*q+9*q**2-4*J)*y**2, lnfamily(4,'y'), y, 2)
if __name__=='__main__':
    for k_,(pr,rf,v,n) in P.items(): compare('CV2007 '+k_, pr, rf, v, n)
