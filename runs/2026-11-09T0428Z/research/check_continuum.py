import numpy as np
from scipy.integrate import solve_ivp
b=-0.1
def rhs(t,y): f,p,q=y; return [p,q,-f*q-b*(1-p*p)]
for s in [0.1,0.2,0.3,0.3192697598,0.35]:
    sol=solve_ivp(rhs,[0,200],[0,0,s],rtol=1e-11,atol=1e-13,dense_output=True)
    ts=[2,5,10,50,100,200 if sol.t[-1]>=200 else sol.t[-1]]
    ps=[sol.sol(t)[1] for t in ts]; qmin=min(sol.y[2]); pmin=min(sol.y[1]); pmax=max(sol.y[1])
    print(s, sol.status, ["%.6f"%v for v in ps], "minq %.2e"%qmin, "p in [%.4f,%.6f]"%(pmin,pmax))
