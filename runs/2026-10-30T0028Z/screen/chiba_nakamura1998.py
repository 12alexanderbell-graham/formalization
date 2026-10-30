"""Chiba & Nakamura, astro-ph/9808022 (PTP 100 (1998) 1077). Transcribed via WebFetch of ar5iv.
Convention: Omega_k0 == k/(a0 H0)^2  (OPPOSITE sign to the modern Omega_k = -k/(a0H0)^2); c0 == jerk j0."""
from common import *
R=sp.Rational
Ok0 = -Ok          # paper's Omega_k0 in terms of standard Omega_k
c0 = j
dL = z + R(1,2)*(1-q)*z**2 + R(1,6)*(3*q**2+q-c0-Ok0-1)*z**3
compare('CN1998 eq2.9-2.11 H0 dL(z)', dL, REF['dL'], z, 3)
# eq 2.5, 2.6: dH/dz|0 = (1+q0)H0 ; d2H/dz2|0 = (c0+3q0+2)H0 - (2+3q0+q0^2)H0
Hz = 1 + (1+q)*z + R(1,2)*((c0+3*q+2)-(2+3*q+q**2))*z**2
compare('CN1998 eq2.3,2.5,2.6 H(z)', Hz, REF['Hz'], z, 2)
