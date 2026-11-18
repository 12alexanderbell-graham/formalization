# Float scan (not evidence): flat LCDM at any Omega in [0,1] (generic model of this run) as a witness
# for open hypotheses of B1FitRL19.rl19_box_unmatched and B1Fit.fit_direction.
from mpmath import mp, mpf, sqrt, log10, log, quad
mp.dps = 15
lam = log10(2); L10 = log(10); k = mpf(20)/3*lam
def dL(O, Z):  # H0 = a0 = 1, flat: (1+z) * int_{sqrt(1/Z)}^1 2/sqrt(O+(1-O)v^6) dv
    return Z*quad(lambda v: 2/sqrt(O+(1-O)*v**6), [sqrt(1/Z), 1])
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def A2(O): return L10*(mpf(3)/2-mpf(3)/4*O)
def A3(O): return L10**2*(mpf(9)/8*O**2-2*O+mpf(7)/6)
def viol(O,a2,a3): return a2-A2(O)+mpf(1)/2 - k*(a3-A3(O))
def spread(ds, xs, a2, a3, sgn=1):
    r=[]
    for d,x in zip(ds,xs):
        b=B(a2,a3,x)*sgn
        if b<=0: return None
        r.append(5*log10(d/b))
    return max(r)-min(r)
Zs=[sqrt(2),2*sqrt(2),4*sqrt(2)]; xs=[log10(z) for z in Zs]
Os=[mpf(i)/20 for i in range(0,21)]
D={O:[dL(O,Z) for Z in Zs] for O in Os}
import itertools
def frange(a,b,n): return [a+(b-a)*i/n for i in range(n+1)]
print('rl19 box, all redshifts fixed, best spread per Omega (sanity, expect > 0.1):')
for O in Os[::4]:
    print(float(O), float(min(spread(D[O],xs,a2,a3) for a2 in frange(3.43,3.49,6) for a3 in frange(1.57,1.69,6))))
print('rl19 drop a2>=3.43 / a2<=3.49 / a3>=1.57 / a3<=1.69: best spread (need <= 0.1)')
for lab,r2,r3 in [('a2<3.43',frange(-3,3.43,80),frange(1.57,1.69,6)),('a2>3.49',frange(3.49,15,80),frange(1.57,1.69,6)),
                  ('a3<1.57',frange(3.43,3.49,6),frange(-5,1.57,80)),('a3>1.69',frange(3.43,3.49,6),frange(1.69,12,80))]:
    best=min(((s,O,a2,a3) for O in Os for a2 in r2 for a3 in r3 for s in [spread(D[O],xs,a2,a3)] if s is not None))
    print(lab,[round(float(v),4) for v in best])
print('rl19 drop z1 (z1 in [0, z3]) / drop z5 (z5 >= z3):')
for lab in ['z1','z5']:
    best=None
    for O in Os:
        for Z in (frange(mpf(1)+mpf(1)/100, 2*sqrt(2), 30) if lab=='z1' else frange(2*sqrt(2), 40, 60)):
            d=dL(O,Z); x=log10(Z)
            if lab=='z1': ds=[d,D[O][1],D[O][2]]; xx=[x,xs[1],xs[2]]
            else: ds=[D[O][0],D[O][1],d]; xx=[xs[0],xs[1],x]
            for a2 in frange(3.43,3.49,3):
                for a3 in frange(1.57,1.69,3):
                    s=spread(ds,xx,a2,a3)
                    if s is not None and (best is None or s<best[0]): best=(s,O,Z,a2,a3)
    print(lab,[round(float(v),4) for v in best])
