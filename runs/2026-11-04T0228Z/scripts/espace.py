# e-space LP: e2 = d2 l^2, e3 = d3 l^3 with d = (a - lus)/l^k; constraints P_k <= rho P_j.
import numpy as np, mpmath as mp
from scipy.optimize import linprog
from explore import D
ell=float(mp.log(2)); l10=float(mp.log(10))
ks=[1,3,5]; f=10**(2*0.05/5)
def Q(Om,u): return u+(1.5-0.75*Om)*u**2+(9/8*Om**2-2*Om+7/6)*u**3
def lp(Om, mu=20/3):
    zs=[2**(k/2)-1 for k in ks]; Ds=[D(Om,z) for z in zs]
    A=[];b=[];lab=[]
    for j in range(3):
        for k in range(3):
            if j==k: continue
            rho=f*Ds[k]/Ds[j]; K,J=ks[k],ks[j]
            A.append([(K**2-rho*J**2)/4,(K**3-rho*J**3)/8]); b.append(-(Q(Om,K*ell/2)-rho*Q(Om,J*ell/2))); lab.append((K,J,rho))
    r=linprog([-1,mu],A_ub=A,b_ub=b,bounds=[(None,None)]*2,method='highs')
    act=[lab[i] for i,m in enumerate(r.ineqlin.marginals) if abs(m)>1e-9]
    return r.fun, act
if __name__=="__main__":
  need=ell**2/l10
  print("need >", need)
  worst=1e9
  for Om in np.linspace(0,1,101):
    v,act=lp(Om); worst=min(worst,v)
    if round(Om*100)%5==0: print(f"{Om:.2f} min={v:.4f} act={[(a[0],a[1],round(a[2],4)) for a in act]}")
  print("worst",worst, "ratio to need", worst/need)
  # RL19 side
  RL=(3.45,1.6)
  L2=np.log10(2)
  print("RL side min over Om of (RL2-T2) - 20/3 log10 2 (RL3-T3):", min((RL[0]-l10*(1.5-0.75*O)) - 20/3*L2*(RL[1]-l10**2*(9/8*O*O-2*O+7/6)) for O in np.linspace(0,1,1001)))
