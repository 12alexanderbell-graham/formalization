# Run 2026-11-26T0628Z: hypothesis 16 of fs_neg_decay_max_shear. Where does an overshooting solution
# (f(0)=p(0)=0, q(0)=s above the attached value) enter the tail region of the planned barrier lemma:
#   p > 1, q < 0, Z = q f + lam (p - 1) > 0, f^2 (lam - b (p + 1)) > lam (p + lam), with b = -beta?
import numpy as np
from scipy.integrate import solve_ivp
for beta,s in [(-0.1,0.4),(-0.1,0.5),(-0.1,0.6),(-0.05,0.5)]:
    b=-beta
    sol=solve_ivp(lambda t,y:[y[1],y[2],-y[0]*y[2]-beta*(1-y[1]**2)],(0,40),[0,0,s],rtol=1e-11,atol=1e-13,dense_output=True,max_step=0.01)
    t=sol.t; f,p,q=sol.y
    best=None
    for lam_mult in [1.5,2,3,4]:
        for i in range(len(t)):
            lam=lam_mult*b*(p[i]+1)
            if p[i]>1 and q[i]<0 and q[i]*f[i]+lam*(p[i]-1)>0 and f[i]**2*(lam-b*(p[i]+1))>lam*(p[i]+lam):
                print(f"beta={beta} s={s} lam={lam:.4f} (x{lam_mult}) first at eta={t[i]:.3f}: f={f[i]:.4f} p={p[i]:.5f} q={q[i]:.6f} Z={q[i]*f[i]+lam*(p[i]-1):.5f} margin={f[i]**2*(lam-b*(p[i]+1))-lam*(p[i]+lam):.4f}")
                break
    print(f"   p at 40: {p[-1]:.5f}, max p {p.max():.4f} at {t[p.argmax()]:.2f}")
