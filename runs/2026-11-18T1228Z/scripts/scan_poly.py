# Float scan (not evidence): rl19_box_unmatched without the law, a = 1/p(t) with p(t) = 1 - t + al t^2 (t <= 0).
# 1 + z = p(t), comoving = int_t^0 p = -t + t^2/2 - al t^3/3 (in units H0 = 1).
from mpmath import mp, mpf, sqrt, log10, findroot
mp.dps=15
Zs=[sqrt(2),2*sqrt(2),4*sqrt(2)]; xs=[log10(z) for z in Zs]
def B(a2,a3,x): return x+a2*x**2+a3*x**3
best=None
for al in [mpf(i)/100 for i in range(-50,300)]:
    ok=True; d=[]
    for Z in Zs:
        # solve 1 - t + al t^2 = Z for t<0: al t^2 - t + (1-Z) = 0
        if al==0: t=1-Z
        else:
            disc=1-4*al*(1-Z)
            if disc<0: ok=False; break
            t=(1-sqrt(disc))/(2*al)
        if t>0: ok=False; break
        # monotone on [t,0]: p'(s) = -1 + 2 al s < 0 for s<=0 if al>=0; if al<0 need -1+2al t <0 -> fine for t<0? -1+2al t = -1 + 2|al||t| 
        if -1+2*al*t>=0: ok=False; break
        chi=-t+t**2/2*0 + (t**2)/2*(-1)*(-1)  # placeholder
        chi=-(t) - (-(t**2)/2) - al*(-(t**3)/3)   # int_t^0 (1 - s + al s^2) ds = -t + t^2/2 - al t^3/3 ... computed below
        chi = (0 - 0 + 0) - (t - t**2/2 + al*t**3/3)
        d.append(Z*chi)
    if not ok: continue
    for a2 in [3.43,3.46,3.49]:
        for a3 in [1.57,1.63,1.69]:
            r=[5*log10(d[i]/B(a2,a3,xs[i])) for i in range(3)]; s=max(r)-min(r)
            if best is None or s<best[0]: best=(s,al,a2,a3)
print([float(v) for v in best])
