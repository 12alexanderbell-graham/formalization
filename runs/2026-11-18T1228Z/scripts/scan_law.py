# Float scan (not evidence): witnesses from the generic curved-LCDM model (any m, k with y > 0)
# for law hypotheses (the model's own density/curvature differ from the parameter), and lower
# density bounds with flat models below the stated range.
from mpmath import mp, mpf, sqrt, log10, log, quad
mp.dps = 12
lam = log10(2); L10 = log(10)
def J(m,k,Z): return quad(lambda v: 2/sqrt(m+k*v**2+(1-m-k)*v**6), [sqrt(1/Z),1])
def ypos(m,k,Z):
    vs=[sqrt(1/Z)+(1-sqrt(1/Z))*i/100 for i in range(101)]
    return min(m+k*v**2+(1-m-k)*v**6 for v in vs)>0
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def A2(O): return L10*(mpf(3)/2-mpf(3)/4*O)
def A3(O): return L10**2*(mpf(9)/8*O**2-2*O+mpf(7)/6)
def fr(a,b,n): return [a+(b-a)*i/n for i in range(n+1)]
ms=fr(mpf('0.02'),mpf(1.5),37); ks=fr(mpf(-1),mpf(1),20)
# (a) rl19 law dropped: box cubic, three redshifts sqrt2, 2sqrt2, 4sqrt2
Zs=[sqrt(2),2*sqrt(2),4*sqrt(2)]; xs=[log10(z) for z in Zs]
best=None
for m in ms:
  for k in ks:
    if not ypos(m,k,Zs[2]): continue
    d=[Z*J(m,k,Z) for Z in Zs]
    for a2 in fr(3.43,3.49,2):
      for a3 in fr(1.57,1.69,2):
        r=[5*log10(d[i]/B(a2,a3,xs[i])) for i in range(3)]; s=max(r)-min(r)
        if best is None or s<best[0]: best=(s,m,k,a2,a3)
print('rl19 law (need <=0.1):',[round(float(t),4) for t in best])
# (b) cubic_direction law dropped: Omega in [0.2,0.4] param, model (m,k); z=3,7. Violation:
# exists cubic with matching ratio and a2-A2 >= 7 lam (a3-A3). Matching line: ratio B7/B3 = d7/d3 * 10^(e/5), |e|<=0.1.
Z3,Z7=mpf(4),mpf(8); x3,x7=log10(Z3),log10(Z7)
def viol_dir(m,k):
    d3=Z3*J(m,k,Z3); d7=Z7*J(m,k,Z7)
    best=None
    for O in fr(mpf(0.2),mpf(0.4),4):
      for e in fr(mpf(-0.1),mpf(0.1),4):
        r=d7/d3*mpf(10)**(e/5)
        # a2 (x7^2 - r x3^2) + a3 (x7^3 - r x3^3) = r x3 - x7 ; scan a3, solve a2
        for a3 in fr(-30,30,240):
            a2=(r*x3-x7-a3*(x7**3-r*x3**3))/(x7**2-r*x3**2)
            if B(a2,a3,x3)<=0 or B(a2,a3,x7)<=0: continue
            v=(a2-A2(O))-7*lam*(a3-A3(O))
            if best is None or v>best[0]: best=(v,O,e,a2,a3)
    return best
bb=None
for m in ms[::2]:
  for k in ks[::2]:
    if not ypos(m,k,Z7): continue
    v=viol_dir(m,k)
    if v and (bb is None or v[0]>bb[0]): bb=(v[0],m,k)+v[1:]
print('cubic_direction law (need >=0):',[round(float(t),4) for t in bb])
# (c) cubic_direction / separation lower bound Omega>=1/5 dropped: flat Omega in (0,0.2)
for O in [mpf(i)/100 for i in [1,3,5,8,10,12,15,18]]:
    v=viol_dir(O,0)
    print('cubic_direction flat O=',float(O),'max viol',round(float(v[0]),4))
