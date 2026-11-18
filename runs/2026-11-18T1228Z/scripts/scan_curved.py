# Float scan (not evidence): curved-pair residual growth 2 S5/S3 * Q3/Q5 for (m, Omega0).
import mpmath as mp
lam = mp.log(2)/mp.log(10)
def Q(a2,a3,a4,x): return x + a2*x**2 + a3*x**3 + a4*x**4
fits = {'sq': (3.075,4.466,-3.716, mp.mpf(10)**(mp.mpf(1)/20)), 'sqg': (3.205,3.564,-2.510, mp.mpf(10)**(mp.mpf(3)/100))}
def J(m,k,w):
    y = lambda v: m + k*v**2 + (1-m-k)*v**6
    return mp.quad(lambda v: 2/mp.sqrt(y(v)), [w,1])
def S(kap,Jv):
    if kap>0: return mp.sin(mp.sqrt(kap)*Jv)/mp.sqrt(kap)
    if kap<0: return mp.sinh(mp.sqrt(-kap)*Jv)/mp.sqrt(-kap)
    return Jv
w3 = mp.sqrt(1/(2*mp.sqrt(2))); w5 = mp.sqrt(1/(4*mp.sqrt(2)))
def growth(m,O0,fit):
    a2,a3,a4,thr = fits[fit]; k = 1-O0
    # require y>0 on [w5,1]
    vs=[w5+(1-w5)*i/200 for i in range(201)]
    if min(m+k*v**2+(1-m-k)*v**6 for v in vs)<=0: return None
    S3=S(O0-1,J(m,k,w3)); S5=S(O0-1,J(m,k,w5))
    if S3<=0 or S5<=0: return None
    g = 2*S5/S3*Q(a2,a3,a4,1.5*lam)/Q(a2,a3,a4,2.5*lam)
    return g/thr  # <=1 means conclusion fails (witness)
import sys
for O0 in [1.0,1.05,1.1,1.2,1.3,1.5,1.7,2.0,2.5,3.0]:
    row=[]
    for m in [0.1,0.2,0.3,0.5,0.7,1.0]:
        r=[growth(m,O0,f) for f in ('sq','sqg')]
        row.append('m=%.1f:%s'%(m,'/'.join('--' if x is None else '%.3f'%x for x in r)))
    print('O0=%.2f '%O0,' '.join(row))
print('open (h8):')
for O0 in [0.0,0.3,0.5,0.7,0.9,0.95]:
    row=[]
    for m in [0.1,0.2,0.3,0.5,0.7,1.0]:
        r=[growth(m,O0,f) for f in ('sq','sqg')]
        row.append('m=%.1f:%s'%(m,'/'.join('--' if x is None else '%.3f'%x for x in r)))
    print('O0=%.2f '%O0,' '.join(row))
print('low m (h1), O0 in [1,1.1]:')
for O0 in [1.0,1.1]:
    for m in [0.0,0.02,0.05,0.08,-0.005]:
        r=[growth(m,O0,f) for f in ('sq','sqg')]
        print(O0,m,r)
