from mpmath import mp, mpf, sqrt, log10, log
mp.dps=20
lam=log10(2); xs=[lam/2, 3*lam/2, 5*lam/2]; Z=[sqrt(2),2*sqrt(2),4*sqrt(2)]
L10=log(10); k=mpf(20)/3*lam
def B(a2,a3,x): return x+a2*x**2+a3*x**3
dS=[z*(z-1) for z in Z]
EdS=[2*z*(1-1/sqrt(z)) for z in Z]
def A2(O): return L10*(mpf(3)/2-mpf(3)/4*O)
def A3(O): return L10**2*(mpf(9)/8*O**2-2*O+mpf(7)/6)
def viol(O,a2,a3): return a2-A2(O)+mpf(1)/2 - k*(a3-A3(O))
import itertools
for name,d,O in [('dS',dS,0),('EdS',EdS,1)]:
  for drop in range(3):
    keep=[i for i in range(3) if i!=drop]
    best=None
    for a2 in [mpf(i)/4 for i in range(-200,200)]:
      for a3 in [mpf(i)/4 for i in range(-200,200)]:
        Bs=[B(a2,a3,x) for x in xs]
        if min(Bs)<=0: continue
        r=[5*log10(d[i]/Bs[i]) for i in keep]
        s=abs(r[0]-r[1])
        v=viol(O,a2,a3)
        if s<=0.06 and v>=0.3:
          sc=min(0.1-s, v/10, min(Bs))
          if best is None or sc>best[0]: best=(sc,a2,a3,s,v,Bs)
    print(name,'drop hm',drop+1,best)
