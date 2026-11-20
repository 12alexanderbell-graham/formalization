import sys
from decimal import Decimal as D, getcontext
getcontext().prec=50
ORD=int(sys.argv[1]); FR=D(sys.argv[2])  # order, step fraction h=FR*s
# initial series at s0=1/2
N=60
a=[D(0)]*(N+1); e=[D(0)]*(N+1); e[0]=D(1)
for k in range(1,N+1):
    a[k]=-e[k-1]/(2*k*(2*k+1))
    e[k]=sum(j*a[j]*e[k-j] for j in range(1,k+1))/k
s=D(1)/2
W=sum(a[k]*s**(2*k) for k in range(N+1))
p=sum(2*k*a[k]*s**(2*k-1) for k in range(1,N+1))
def taylor(s,W,p):
    Wc=[W]; pc=[p]; E=[W.exp()]
    for k in range(ORD):
        # (k+1) s p_{k+1} = -(k+2) p_k... derive: s p' + 2p + sE=0, coeff tau^k:
        # s*(k+1)p_{k+1} + k p_k + 2 p_k + s E_k + E_{k-1} = 0
        rhs=-( (k+2)*pc[k] + s*E[k] + (E[k-1] if k>=1 else 0))
        pc.append(rhs/(s*(k+1)))
        Wc.append(pc[k]/(k+1))
        kk=k+1
        E.append(sum(pc[j-1]*E[kk-j] for j in range(1,kk+1))/kk)
    return Wc,pc
def ev(c,t):
    r=D(0)
    for x in reversed(c): r=r*t+x
    return r
def dev(c,t):
    r=D(0)
    for k in range(len(c)-1,0,-1): r=r*t+k*c[k]
    return r
roots=[]
def g(pc,s,t): return 2+(s+t)*ev(pc,t)
def gp(pc,s,t): return ev(pc,t)+(s+t)*dev(pc,t)
prevg=2+s*p
log=[]
while len(roots)<4 and s<6000:
    h=FR*s
    Wc,pc=taylor(s,W,p)
    # sample
    M=8
    pt=D(0); pg=g(pc,s,pt)
    for i in range(1,M+1):
        t=h*i/M; cg=g(pc,s,t)
        if pg*cg<0:
            x=(pt+t)/2
            for _ in range(60):
                x=x-g(pc,s,x)/gp(pc,s,x)
            Wz=ev(Wc,x); sz=s+x
            roots.append((sz,sz*sz*Wz.exp()))
        pt,pg=t,cg
    W=ev(Wc,h); p=ev(pc,h); s=s+h
    # check u,v region
    v=-s*p; u=s*W.exp()/(-p) if p!=0 else None
    log.append((s,u,v))
for z,l in roots: print('zeta',f"{z:.25f}",'lam',f"{l:.25f}")
import pickle
# u,v scans: restart finer
