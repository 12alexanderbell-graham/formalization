from mpmath import mp, mpf, sqrt, log10, quad
mp.dps=30
Om=mpf(100)
g=lambda v: 2/sqrt(Om+(1-Om)*v**6)
v3=1/sqrt(2*sqrt(2)); v5=1/sqrt(4*sqrt(2))
J3=quad(g,[v3,0.9,0.99,0.999,1]); K=quad(g,[v5,v3]); print('J5/J3',(J3+K)/J3)
lam=log10(2)
def Bq(c,x): return x+c[0]*x**2+c[1]*x**3+c[2]*x**4
for c,thr in [((3.075,4.466,-3.716),0.25),((3.205,3.564,-2.510),0.15)]:
    B3=Bq(c,1.5*lam); B5=Bq(c,2.5*lam)
    R=10**(thr/5)*B5/(2*B3); print('need J5/J3 <=',R,' actual', (J3+K)/J3, 'D', 5*log10(2*(J3+K)/J3*B3/B5))
def grid(a,b,n,geo):
    # points from a to b, geometric toward b
    pts=[a]
    for i in range(1,n+1):
        t=mpf(i)/n
        pts.append(b-(b-a)*(1-t)**geo if geo else a+(b-a)*t)
    return pts
for n,geo in [(10,2),(20,2),(20,3),(30,3),(40,3)]:
    p=grid(mpf('0.5947'),1,n,geo)
    lo=sum((p[i+1]-p[i])*g(p[i]) for i in range(n))
    q=grid(mpf('0.4204'),mpf('0.5947'),4,0)
    up=sum((q[i+1]-q[i])*g(q[i+1]) for i in range(4))
    print(n,geo,'J3lo/J3',lo/J3,'bound ratio',(lo+up)/lo)
