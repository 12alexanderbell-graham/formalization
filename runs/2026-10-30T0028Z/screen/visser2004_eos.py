"""Visser gr-qc/0309109 (CQG 21 (2004) 2603): Eq.(25) kappa0, Eq.(28)/(29) d^2p/drho^2, Eq.(46) dL.
Transcribed via WebFetch (term-by-term listing of PDF). Units 8 pi G = c = 1."""
import sympy as sp
from common import *
t=sp.symbols('t'); H,a0,k=sp.symbols('H a0 k',positive=True)
A=sp.Function('A')(t)
rho = 3*((A.diff(t)/A)**2 + k/A**2)
p = -(2*A.diff(t,2)/A + (A.diff(t)/A)**2 + k/A**2)
rd, pd = rho.diff(t), p.diff(t)
kappa = pd/rd
d2 = kappa.diff(t)/rd
vals = {A.diff(t,n): a0*v*H**n for n,v in [(5,l),(4,s),(3,j),(2,-q),(1,1)]}
def at0(e):
    for n in (5,4,3,2,1): e = e.subs(A.diff(t,n), vals[A.diff(t,n)])
    return sp.simplify(e.subs(A,a0))
K = k/(H**2*a0**2)
kap0 = at0(kappa); d20 = at0(d2); rho0 = at0(rho)
P25 = -sp.Rational(1,3)*(1-j+K)/(1+q+K)
print('Eq25 kappa0 diff:', sp.simplify(kap0-P25))
P28 = -(1+K)*(s*(1+q)+j*(1+j+4*q+q**2)+q*(1+2*q)+(s+j+q+q*j)*K)/(6*rho0*(1+q+K)**3)
print('Eq28 d2p/drho2 diff:', sp.simplify(d20-P28))
P29 = -(s*(1+q)+j*(1+j+4*q+q**2)+q*(1+2*q))/(6*rho0*(1+q)**3)
print('Eq29 (k=0) diff:', sp.simplify((d20-P29).subs(k,0)))
# Eq 46 d_L
R=sp.Rational; KK=-Ok
P46 = z*(1+R(1,2)*(1-q)*z - R(1,6)*(1-q-3*q**2+j+KK)*z**2 + R(1,24)*(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*KK*(1+3*q))*z**3)
compare('Visser2004 eq46 dL(z)', P46, REF['dL'], z, 4)
