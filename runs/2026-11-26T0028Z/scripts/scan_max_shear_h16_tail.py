# Long-range check: beta=-0.1, s above the attached value; does p return to 1 (algebraically)?
import numpy as np
from scipy.integrate import solve_ivp
beta=-0.1
def F(t,y): f,p,q=y; return [p,q,-f*q-beta*(1-p*p)]
for s in [0.35,0.5,1.0]:
    sol=solve_ivp(F,(0,1e4),[0,0,s],method='LSODA',rtol=1e-10,atol=1e-14,dense_output=True)
    for T in [12,100,1000,1e4]:
        f,p,q=sol.sol(T); print(f"s={s} eta={T:g} p-1={p-1:.4e} q={q:.3e} (p-1)*eta^(2|beta|)={(p-1)*T**(2*abs(beta)):.4f}")
