from mpmath import mp, mpf, sqrt, log10, log, quad
import itertools
mp.dps=20
lam=log10(2); xs=[lam/2, 3*lam/2, 5*lam/2]; Z=[sqrt(2),2*sqrt(2),4*sqrt(2)]
def dist(Om):
    E=lambda z: sqrt(Om*(1+z)**3+1-Om)
    return [z*quad(lambda u:1/E(u),[0,z-1]) for z in Z]
L10=log(10)
def A2(O): return L10*(mpf(3)/2-mpf(3)/4*O)
def A3(O): return L10**2*(mpf(9)/8*O**2-2*O+mpf(7)/6)
k=mpf(20)/3*lam
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def spread(d,a2,a3,idx=(0,1,2)):
    r=[5*log10(d[i]/B(a2,a3,xs[i])) for i in idx]
    return max(r)-min(r)
def viol(O,a2,a3): return a2-A2(O)+0.5 - k*(a3-A3(O))   # >=0 violates
for O in [0,1,mpf('0.3')]:
    d=dist(O); print('Omega',O,'A2',A2(O),'A3',A3(O))
    # exact fit all three: solve ratio eqs
    import mpmath
    # find a2,a3 with B_i ∝ d_i : B3/B1=d3/d1, B5/B1=d5/d1
    f=lambda a2,a3: [B(a2,a3,xs[1])*d[0]-B(a2,a3,xs[0])*d[1], B(a2,a3,xs[2])*d[0]-B(a2,a3,xs[0])*d[2]]
    s=mpmath.findroot(f,(3,2)); a2,a3=s
    print(' exact fit',a2,a3,'viol',viol(O,a2,a3))
