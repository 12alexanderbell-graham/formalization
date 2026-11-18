from mpmath import mp, mpf, sqrt, log10, log, quad, findroot
mp.dps=20
lam=log10(2); xs=[lam/2, 3*lam/2, 5*lam/2]; Z=[sqrt(2),2*sqrt(2),4*sqrt(2)]
L10=log(10)
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def r(d,a2,a3): return [5*log10(abs(d[i]/B(a2,a3,xs[i]))) if B(a2,a3,xs[i])!=0 else 0 for i in range(3)]
def powlaw(p):
    if p==1: return [z*log(z) for z in Z]
    q=(1-p)/p
    return [z*(z**q-1)/q for z in Z]
def exactfit(d):
    f=lambda a2,a3: [B(a2,a3,xs[1])*d[0]-B(a2,a3,xs[0])*d[1], B(a2,a3,xs[2])*d[0]-B(a2,a3,xs[0])*d[2]]
    return findroot(f,(1,3))
for p in [mpf(1)/2, mpf(2)/3, mpf('0.8'), mpf('0.9'), 1, mpf('1.2'), 2, 3]:
    print(p, exactfit(powlaw(p)))
# spread for box corners at Omega grid
import itertools
def distO(Om):
    E=lambda z: sqrt(Om*(1+z)**3+1-Om)
    return [z*quad(lambda u:1/E(u),[0,z-1]) for z in Z]
for O in [0, 0.5, 0.8,1]:
    d=distO(O); 
    best=None
    for a2 in [3.3,3.35,3.40,3.43,3.46,3.49,3.55,3.6]:
        for a3 in [1.4,1.5,1.57,1.63,1.69,1.8,1.9]:
            rr=r(d,a2,a3); s=max(rr)-min(rr)
            print(O,a2,a3,round(float(s),4))
