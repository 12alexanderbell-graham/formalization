import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
# W'' + (2/s)W' + e^W = 0, W(0)=0, W'(0)=0. Series: W = -s^2/6 + s^4/120 - ...
s0=1e-3
W0=-s0**2/6+s0**4/120; dW0=-s0/3+s0**3/30
def f(s,y): return [y[1], -2/s*y[1]-np.exp(y[0])]
# event: lambda'(s)=0 <=> 2 + s W' = 0
def ev(s,y): return 2+s*y[1]
S=1e6
sol=solve_ivp(f,(s0,S),[W0,dW0],method='DOP853',rtol=1e-13,atol=1e-14,events=ev,dense_output=True)
lam=lambda s: s*s*np.exp(sol.sol(s)[0])
z=sol.t_events[0]; lz=[s*s*np.exp(y[0]) for s,y in zip(z,sol.y_events[0])]
for k in range(min(8,len(z))): print(f"zeta_{k} = {z[k]:.10f}  lambda = {lz[k]:.10f}")
print("number of turning points up to",S,":",len(z)," last |lambda-2| =",abs(lz[-1]-2))
grid=np.concatenate([[s0],z,[S]])
def count(L):
    roots=[]
    for a,b in zip(grid[:-1],grid[1:]):
        fa,fb=lam(a)-L,lam(b)-L
        if fa==0: roots.append(a)
        if fa*fb<0: roots.append(brentq(lambda s:lam(s)-L,a,b,xtol=1e-14))
    return roots
lstar,l1,l2=lz[0],lz[1],lz[2]
for L in [1,1.5,l1-0.01,l2+0.01,3,3.3,lstar-1e-9]:
    r=count(L); print(f"lambda={L:.10f}: {len(r)} radii {np.round(r,6)}")
