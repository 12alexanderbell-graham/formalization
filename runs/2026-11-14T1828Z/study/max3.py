"""Float study (unchecked): third maximum of the Bonnor-Ebert mass from BEOChain's state at 20000."""
import numpy as np, math
from scipy.integrate import solve_ivp
def f(t,y):
    u,v=y; return [u*(3-u-v), v*(u-1)]
def g(t,y): return 2*y[0]-y[1]
g.direction=-1
t0=math.log(20000)
sol=solve_ivp(f,[t0,math.log(3e6)],[1.005687661,1.989078226],rtol=1e-13,atol=1e-15,events=g,dense_output=True)
for te,ye in zip(sol.t_events[0],sol.y_events[0]):
    s=math.exp(te); u,v=ye; P=u*v**3; m=math.sqrt(P/(4*math.pi))
    print('max at s=%.6f u=%.10f v=%.10f m=%.10f contrast=%.6f'%(s,u,v,m,s*s/(2*u*u)))
def V(u,v): return u+v-math.log(u)-2*math.log(v/2)
# max of u v^3 on sublevel set of V through state at T
for T in [100000,120000,150000,200000,250000,300000]:
    u,v=sol.sol(math.log(T)); lev=V(u,v)
    # maximize log u + 3 log v subject to V<=lev: grid
    best=0
    for uu in np.linspace(0.9,1.1,2001):
        # solve v on boundary: v - 2 log(v/2) = lev - uu + log uu ; two roots around 2
        r=lev-uu+math.log(uu)
        if r<2: continue
        lo,hi=2.0,4.0
        for _ in range(60):
            mid=(lo+hi)/2
            if mid-2*math.log(mid/2)<r: lo=mid
            else: hi=mid
        best=max(best,uu*lo**3)
    print('T',T,'u v',u,v,'P',u*v**3,'maxP on sublevel',best)
