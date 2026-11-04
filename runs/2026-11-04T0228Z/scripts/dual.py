import numpy as np
from scipy.optimize import linprog
from explore import D, T
import sys
eps=0.05; s=float(sys.argv[1]) if len(sys.argv)>1 else 0.2
ks=[int(c) for c in (sys.argv[2] if len(sys.argv)>2 else "12345")]
zs=[2**(k/2)-1 for k in ks]
xs=[np.log10(1+z) for z in zs]
def run(Om):
    Ds=[D(Om,z) for z in zs]; f=10**(2*eps/5)
    A=[];b=[];lab=[]
    for j in range(len(zs)):
        for k in range(len(zs)):
            if j==k: continue
            rho=f*Ds[k]/Ds[j]
            A.append([xs[k]**2-rho*xs[j]**2, xs[k]**3-rho*xs[j]**3]); b.append(-(xs[k]-rho*xs[j])); lab.append(f"P{ks[k]}<=r P{ks[j]}")
    n=np.array([-s,1.0])
    r=linprog(n,A_ub=A,b_ub=b,bounds=[(None,None)]*2,method='highs')
    if r.status!=0: return None
    act=[lab[i] for i,m in enumerate(r.ineqlin.marginals) if abs(m)>1e-9]
    return r.fun-n@T(Om), r.x, act
for Om in np.linspace(0.0,1.0,21):
    out=run(Om)
    print(f"{Om:.2f}", "infeasible" if out is None else f"margin={out[0]:.3f} x=({out[1][0]:.2f},{out[1][1]:.2f}) act={out[2]}")
