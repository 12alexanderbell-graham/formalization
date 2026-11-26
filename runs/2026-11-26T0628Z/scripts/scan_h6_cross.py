# Run 2026-11-26T0628Z: hypothesis 6, the sign of s_att - q_rev(eta*) over beta (eta*: where the reversed-flow
# solution's f returns to zero); positive means the translated reversed solution is a witness with the attached second.
import numpy as np
from scipy.integrate import solve_ivp
exec(open('scan_h6_h13.py').read().split('for beta in')[0])
for beta in [-0.06,-0.07,-0.08,-0.09,-0.095]:
    sa=shoot(beta,0.0,1.0)
    ss=np.linspace(-0.4,0.0,401); pe=[end(beta,s) for s in ss]; rev=None
    for i in range(len(ss)-1):
        if (pe[i]-1)*(pe[i+1]-1)<0 and ss[i]<0:
            lo,hi=(ss[i],ss[i+1]) if pe[i]<1 else (ss[i+1],ss[i])
            for _ in range(80):
                m=(lo+hi)/2
                if end(beta,m)<1: lo=m
                else: hi=m
            rev=(lo+hi)/2
    sol=solve_ivp(F(beta),(0,10),[0,0,rev],rtol=1e-12,atol=1e-14,max_step=0.005)
    t=sol.t; f,p,q=sol.y
    k=np.where((f[:-1]<0)&(f[1:]>=0)&(t[:-1]>0.01))[0][0]
    print(f"beta={beta}: s_att={sa:.6f} q_rev(eta*={t[k]:.3f})={q[k]:.6f} margin={sa-q[k]:+.6f}")
