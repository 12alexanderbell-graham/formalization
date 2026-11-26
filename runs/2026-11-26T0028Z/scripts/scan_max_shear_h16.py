# Scan: beta<0, shooting f(0)=p(0)=0, q(0)=s >= attached value; does p tend to 1 (a BVP solution outside q>0)?
import numpy as np
from scipy.integrate import solve_ivp
def run(beta,s,T=12):
    def F(t,y): f,p,q=y; return [p,q,-f*q-beta*(1-p*p)]
    ev=lambda t,y: abs(y[1])-50; ev.terminal=True
    sol=solve_ivp(F,(0,T),[0,0,s],rtol=1e-10,atol=1e-12,events=ev,max_step=0.05)
    p=sol.y[1]; q=sol.y[2]
    return sol.t[-1], p[-1], q.min(), p.max()
for beta in [-0.05,-0.1,-0.15,-0.19]:
    print('beta',beta)
    for s in np.concatenate([np.linspace(0.0,1.0,21),[1.5,2,3,5]]):
        t,pe,qmin,pmax=run(beta,s)
        print(f"  s={s:.3f} t_end={t:6.2f} p_end={pe:9.4f} pmax={pmax:8.3f} qmin={qmin:9.4f}")
