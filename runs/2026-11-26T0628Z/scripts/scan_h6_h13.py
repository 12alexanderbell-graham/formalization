# Run 2026-11-26T0628Z: scan for hypotheses 6 (p(0)=0) and 13 (f2(0)=0) of fs_neg_decay_max_shear.
# Idea: translate the reversed-flow solution (q(0)<0, p->1 fast) so that a translated copy meets the other
# wall conditions: (13) start at its zero of p after the minimum (f2(0)=g(eta_z) != 0, p2(0)=0, q2>0);
# (6) start where g returns to zero (f(0)=0, p(0)=a>0, q>0, fast decay). Compare with the attached shear.
import numpy as np
from scipy.integrate import solve_ivp
def F(beta):
    return lambda t,y: [y[1], y[2], -y[0]*y[2]-beta*(1-y[1]**2)]
def end(beta,s,T=10):
    ev=lambda t,y: abs(y[1])-3; ev.terminal=True
    sol=solve_ivp(F(beta),(0,T),[0,0,s],rtol=1e-12,atol=1e-14,events=ev)
    return sol.y[1][-1]
def shoot(beta,lo,hi,T=10):
    # lo undershoots (p_end<1), hi overshoots
    for _ in range(80):
        m=(lo+hi)/2
        if end(beta,m,T)<1: lo=m
        else: hi=m
    return (lo+hi)/2
for beta in [-0.02,-0.05,-0.1,-0.15,-0.19]:
    sa=shoot(beta,0.0,1.0)
    # reversed: below the attached value, the map s->p_end is not monotone; scan for undershoot/overshoot pairs in s<0
    ss=np.linspace(-0.4,0.0,401); pe=[end(beta,s) for s in ss]
    rev=None
    for i in range(len(ss)-1):
        if (pe[i]-1)*(pe[i+1]-1)<0 and ss[i]<0:
            lo,hi=(ss[i],ss[i+1]) if pe[i]<1 else (ss[i+1],ss[i])
            for _ in range(80):
                m=(lo+hi)/2
                if end(beta,m)<1: lo=m
                else: hi=m
            rev=(lo+hi)/2
    if rev is None:
        print(f"beta={beta}: attached {sa:.6f}, no reversed found"); continue
    sol=solve_ivp(F(beta),(0,10),[0,0,rev],rtol=1e-12,atol=1e-14,dense_output=True,max_step=0.01)
    t=sol.t; f,p,q=sol.y
    iz=np.where((p[:-1]<=0)&(p[1:]>0)&(t[:-1]>0.01))[0]
    i0=np.where((f[:-1]<0)&(f[1:]>=0)&(t[:-1]>0.01))[0]
    out=f"beta={beta}: attached s={sa:.6f}, reversed s={rev:.6f}"
    if len(iz):
        k=iz[0]; out+=f" | h13: eta_z={t[k]:.4f} f2(0)={f[k]:.5f} q2(0)={q[k]:.6f} q2>0 after: {q[k:].min()>0} -> q2(0)>s_att? {q[k]>sa}"
    if len(i0):
        k=i0[0]; out+=f" | h6: eta*={t[k]:.4f} p(0)={p[k]:.5f} q(0)={q[k]:.6f} qmin after={q[k:].min():.3g} -> q(0)<s_att? {q[k]<sa}"
    print(out)
