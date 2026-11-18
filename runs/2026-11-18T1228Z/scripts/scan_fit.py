# Float scan (not evidence): B1Fit.fit_direction without 0 < H (13) or one positivity condition (14-16),
# flat LCDM at any Omega in [0,1]; and refinement of the rl19 a3<=1.69 drop.
from mpmath import mp, mpf, sqrt, log10, log, quad, findroot
mp.dps = 15
lam = log10(2); L10 = log(10); k = mpf(20)/3*lam
def dL(O, Z): return Z*quad(lambda v: 2/sqrt(O+(1-O)*v**6), [sqrt(1/Z), 1])
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def A2(O): return L10*(mpf(3)/2-mpf(3)/4*O)
def A3(O): return L10**2*(mpf(9)/8*O**2-2*O+mpf(7)/6)
def viol(O,a2,a3): return a2-A2(O)+mpf(1)/2 - k*(a3-A3(O))
Zs=[sqrt(2),2*sqrt(2),4*sqrt(2)]; xs=[log10(z) for z in Zs]
Os=[mpf(i)/20 for i in range(0,21)]
D={O:[dL(O,Z) for Z in Zs] for O in Os}
def fr(a,b,n): return [a+(b-a)*i/n for i in range(n+1)]
def resid(d,b):  # Real.logb of |.|, junk 0 at 0
    if b==0: return mpf(0)
    return 5*log10(abs(d/b))
# H<0: all B<0 ; residuals use |B| with H=-1 scale absorbed by offset
best=None
for O in Os:
    for a2 in fr(-40,10,100):
        for a3 in fr(-80,40,120):
            Bs=[B(a2,a3,x) for x in xs]
            if max(Bs)>=0: continue
            v=viol(O,a2,a3)
            if v<0: continue
            r=[resid(D[O][i],Bs[i]) for i in range(3)]; s=max(r)-min(r)
            if best is None or s<best[0]: best=(s,O,a2,a3,v)
print('H<0',[round(float(t),4) for t in best])
# hp_i dropped: B_i<0 (abs), H>0
for i in range(3):
    best=None
    for O in Os:
        for a2 in fr(-40,10,100):
            for a3 in fr(-80,40,120):
                Bs=[B(a2,a3,x) for x in xs]
                if Bs[i]>=0 or min(Bs[j] for j in range(3) if j!=i)<=0: continue
                v=viol(O,a2,a3)
                if v<0: continue
                r=[resid(D[O][j],Bs[j]) for j in range(3)]; s=max(r)-min(r)
                if best is None or s<best[0]: best=(s,O,a2,a3,v)
    print('hp',i+1,'B<0',[round(float(t),4) for t in best] if best else None)
# hp_i dropped with B_i = 0 exactly (junk logb 0 = 0): need |c|<=0.05 and other two within 0.05 of c,
# with H free: residual_j = 5log10(d_j H/(L10 B_j)); choose H so the two others are centred at 0:
for i in range(3):
    best=None
    for O in Os:
        for a3 in fr(-60,60,600):
            a2=-(1+a3*xs[i]**2)/xs[i]
            Bs=[B(a2,a3,x) for x in xs]
            if min(Bs[j] for j in range(3) if j!=i)<=0: continue
            v=viol(O,a2,a3)
            if v<0: continue
            r=[5*log10(D[O][j]/(L10*Bs[j])) for j in range(3) if j!=i]
            s=abs(r[0]-r[1])   # need <= 0.1 (then H centres them on 0 and c = 0)
            if best is None or s<best[0]: best=(s,O,a2,a3,v)
    print('hp',i+1,'B=0',[round(float(t),4) for t in best] if best else None)
# rl19 a3<=1.69 dropped: refine
best=None
for O in fr(mpf(0.05),mpf(0.4),35):
    d=[dL(O,Z) for Z in Zs]
    for a2 in fr(3.43,3.49,6):
        for a3 in fr(3,12,90):
            r=[5*log10(d[j]/B(a2,a3,xs[j])) for j in range(3)]; s=max(r)-min(r)
            if best is None or s<best[0]: best=(s,O,a2,a3)
print('rl19 a3>1.69 refined',[round(float(t),4) for t in best])
