"""Vitagliano, Xia, Liberati, Viel, 'High-redshift cosmography', arXiv:0911.1249 (JCAP 03 (2010) 005).
Transcribed via WebFetch of ar5iv.labs (LaTeX). Omega_0 = 1 + kc^2/(H0^2 a0^2) = 1 - Omega_k."""
from common import *
R=sp.Rational; O0=1-Ok; K=-Ok
dLz = z + R(1,2)*(1-q)*z**2 - R(1,6)*(1-q-3*q**2+j+K)*z**3 + R(1,24)*(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*K*(1+3*q))*z**4
compare('VXLV2010 eq4 dL(z)', dLz, REF['dL'], z, 4)
dLy = y - R(1,2)*(q-3)*y**2 + R(1,6)*(12-5*q+3*q**2-(j+O0))*y**3 + R(1,24)*(60-7*j-10*O0-32*q+10*q*j+6*q*O0+21*q**2-15*q**3+s)*y**4
compare('VXLV2010 eq9 dL(y)', dLy, REFY['dL'], y, 4)
lny = -R(1,2)*(q-3)*y + R(1,24)*(21-4*(j+O0)+q*(9*q-2))*y**2 + R(1,24)*(15+4*O0*(q-1)+j*(8*q-1)-5*q+2*q**2-10*q**3+s)*y**3
compare('VXLV2010 eq10/11 ln(dL/y), mu(y)', lny, ser(REFY['lnDLoverZ'] - sp.log(1-y), y, 5), y, 3)
