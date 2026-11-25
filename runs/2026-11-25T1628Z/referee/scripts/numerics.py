# Own Taylor-series integrator for the homology system in t = log s:
#   u' = u(3-u-v), v' = v(u-1); extrema of m at zeros of g = 2u - v.
import sys
from mpmath import mp, mpf, exp, log, sqrt, pi, nstr
def run(dps, order, h):
    mp.dps = dps
    # Lane-Emden series W = sum a_n s^{2n}
    N=60; a=[mpf(0)]*(N+1); E=[mpf(0)]*(N+1); E[0]=mpf(1)
    for n in range(N):
        a[n+1] = -E[n]/(2*(n+1)*(2*n+3))
        m=n+1; E[m]=sum(k*a[k]*E[m-k] for k in range(1,m+1))/m
    s0=mpf('0.05')
    W=sum(a[n]*s0**(2*n) for n in range(N+1))
    Wp=sum(2*n*a[n]*s0**(2*n-1) for n in range(1,N+1))
    u=s0*exp(W)/(-Wp); v=-s0*Wp; t=log(s0)
    def taylor(u,v):
        U=[u]; V=[v]
        for k in range(order):
            uu=sum(U[i]*U[k-i] for i in range(k+1)); uv=sum(U[i]*V[k-i] for i in range(k+1))
            U.append((3*U[k]-uu-uv)/(k+1)); V.append((uv-V[k])/(k+1))
        return U,V
    ev=lambda C,x: sum(c*x**i for i,c in reversed(list(enumerate(C)))) if False else horner(C,x)
    def horner(C,x):
        r=mpf(0)
        for c in reversed(C): r=r*x+c
        return r
    res=[]
    while len(res)<16:
        U,V=taylor(u,v)
        G=[2*U[i]-V[i] for i in range(len(U))]
        g0=G[0]; g1=horner(G,h)
        if g0!=0 and g0*g1<0:
            # bisection then Newton on Taylor polynomial
            lo,hi=mpf(0),h
            for _ in range(60):
                mid=(lo+hi)/2
                if horner(G,mid)*g0>0: lo=mid
                else: hi=mid
            r=(lo+hi)/2
            dG=[i*G[i] for i in range(1,len(G))]
            for _ in range(8): r-=horner(G,r)/horner(dG,r)
            ur=horner(U,r); vr=horner(V,r)
            res.append((t+r, ur, vr))
        u=horner(U,h); v=horner(V,h); t+=h
    return res
A=run(40,40,mpf('0.05'))
B=run(50,50,mpf('0.025'))
mp.dps=40
ms=sqrt(2/pi); R=exp(2*pi/sqrt(7)); D=-exp(-pi/sqrt(7))
print("exp(2pi/sqrt7) =",nstr(R,25)); print("-exp(-pi/sqrt7)=",nstr(D,25))
prev=None
for k,((ta,ua,va),(tb,ub,vb)) in enumerate(zip(A,B)):
    xi=exp(tb); m=sqrt(ub*vb**3/(4*pi)); dev=m-ms
    err=max(abs(exp(ta)/xi-1), abs(ua-ub))
    line=f"k={k:2d} xi={nstr(xi,25)} m={nstr(m,25)} m-ms={nstr(dev,8)} relerr~{nstr(err,3)}"
    if prev:
        line+=f"\n      ratio={nstr(xi/prev[0],22)} (R diff {nstr(xi/prev[0]-R,3)})  devq={nstr(dev/prev[1],22)} (diff {nstr(dev/prev[1]-D,3)})"
    print(line); prev=(xi,dev)
