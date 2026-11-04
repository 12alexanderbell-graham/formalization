import numpy as np
from explore import feas, T, zs
RL = np.array([3.45,1.6])
Oms = np.linspace(0.0,1.0,21)
for eps in [0.05,0.1]:
  for s in [0.1,0.2,0.3,0.5,0.75,1.0]:
    n = np.array([-s,1.0])  # ell = a3 - s a2
    A=1e9;B=1e9;C=1e9
    for Om in Oms:
        r=feas(Om,zs,eps,n)
        if r.status!=0: print("infeasible",Om); continue
        lT = n@T(Om); A=min(A,r.fun-lT); B=min(B,lT-n@RL); C=min(C,r.fun-n@RL)
    print(f"eps={eps} s={s}: min(ell_F-ell_T)={A:.3f}  min(ell_T-ell_RL)={B:.3f}  min(ell_F-ell_RL)={C:.3f}")
