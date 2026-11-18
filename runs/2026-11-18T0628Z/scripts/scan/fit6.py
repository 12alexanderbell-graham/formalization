from mpmath import mp, mpf, sqrt, log10, log
from fractions import Fraction as F
mp.dps=25
lam=log10(2); xs=[lam/2, 3*lam/2, 5*lam/2]; L10=log(10); k=mpf(20)/3*lam
rho=mpf(2)**(mpf(1)/4)
d=[3*(rho**2-rho), 6*(rho**2-1/rho), 12*rho**2-6*rho]
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def A2(O): return L10*(mpf(3)/2-mpf(3)/4*O)
def A3(O): return L10**2*(mpf(9)/8*O**2-2*O+mpf(7)/6)
def viol(O,a2,a3): return a2-A2(O)+mpf(1)/2 - k*(a3-A3(O))
def best(keep,O,box=None,grid=None):
    res=None
    for a2,a3 in grid:
        Bs=[B(a2,a3,x) for x in xs]
        if min(Bs[i] for i in range(3))<=0.05: continue
        if box is None:
            v=viol(O,a2,a3)
            if v<0.5: continue
        q=[d[i]/(L10*Bs[i]) for i in keep]  # y_i = H*q_i
        lo,hi=min(q),max(q); ratio=hi/lo
        if res is None or ratio<res[0]: res=(ratio,a2,a3,lo,hi)
    ratio,a2,a3,lo,hi=res
    H=2/(lo+hi)   # center
    return dict(a2=a2,a3=a3,ratio=float(ratio),H=float(H),ys=[float(H*d[i]/(L10*B(a2,a3,xs[i]))) for i in range(3)], viol=float(viol(O,a2,a3)) if box is None else None)
g=[(mpf(i)/4,mpf(j)/4) for i in range(-100,200) for j in range(-100,100)]
print('W17 keep 3,5', best([1,2],1,grid=g))
print('W18 keep 1,5', best([0,2],1,grid=g))
print('W19 keep 1,3', best([0,1],1,grid=g))
print('W9 all, O=0', best([0,1,2],0,grid=g))
gb=[(mpf(a)/100,mpf(b)/100) for a in range(343,350) for b in range(157,170)]
print('rl19 W11 keep 1,5', best([0,2],1,box=True,grid=gb))
