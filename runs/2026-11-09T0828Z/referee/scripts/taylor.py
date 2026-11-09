"""High-order Taylor integrator (mpmath) for scaled Falkner-Skan beta<0:
   f'=p, p'=q, q'=-K f q + 1 - p^2,  f(0)=p(0)=0, q(0)=alpha.
Event classification Over / Slow (mu=3, theta=(mu+2/mu)/K) on a grid h, with dense
sampling inside each step for the Over / p<1 checks (float-level, not rigorous)."""
import sys, mpmath as mp
mp.mp.dps = 50

def taylor_step(f, p, q, K, h, N):
    F=[f]; P=[p]; Q=[q]
    for n in range(N):
        fq = mp.fsum(F[i]*Q[n-i] for i in range(n+1))
        pp = mp.fsum(P[i]*P[n-i] for i in range(n+1))
        F.append(P[n]/(n+1)); P.append(Q[n]/(n+1))
        Q.append((-K*fq + (1 if n==0 else 0) - pp)/(n+1))
    return F,P,Q

def ev(C, x):
    s = mp.mpf(0)
    for c in reversed(C): s = s*x + c
    return s

def run(alpha, K=10, mu=3, h=mp.mpf(1)/32, N=30, smax=20, sub=8, stop=True, trace=False):
    K=mp.mpf(K); mu=mp.mpf(mu); theta=(mu+2/mu)/K
    f=mp.mpf(0); p=mp.mpf(0); q=mp.mpf(alpha); s=mp.mpf(0)
    pmax=mp.mpf(0); first_slow=None; out=[]
    while s < smax:
        F,P,Q = taylor_step(f,p,q,K,h,N)
        # dense check for Over inside the step
        for j in range(1,sub+1):
            x=h*j/sub; pv=ev(P,x)
            if pv>1:
                # refine first crossing p=1 inside the step
                lo=h*(j-1)/sub; hi=x
                for _ in range(80):
                    m=(lo+hi)/2
                    if ev(P,m)>1: hi=m
                    else: lo=m
                # peak of p (q=0) after crossing, within a further window
                return dict(event='Over', s_cross=s+hi, node=s+h, P_node=ev(P,h), Q_node=ev(Q,h), pmax_seen=pmax)
            pmax=max(pmax,pv)
        f,p,q = ev(F,h),ev(P,h),ev(Q,h); s+=h
        if trace: out.append((s,f,p,q))
        if 0<p<1 and q<mu*(1-p) and f>theta and first_slow is None:
            first_slow=dict(event='Slow', node=s, P=p, Q=q, m1=1-p, m2=mu*(1-p)-q, m3=f-theta, F=f)
            if stop: return first_slow
    return first_slow or dict(event='none', s=s, p=p, q=q, f=f)

def shoot(lo, hi, K=10, tol=mp.mpf('1e-30'), **kw):
    """lo, hi have different events; bisect."""
    elo=run(lo,K,**kw)['event']; ehi=run(hi,K,**kw)['event']
    assert elo!=ehi and 'none' not in (elo,ehi), (elo,ehi)
    while hi-lo>tol:
        m=(lo+hi)/2; e=run(m,K,**kw)['event']
        if e=='none': raise RuntimeError('neither at %s'%m)
        if e==elo: lo=m
        else: hi=m
    return lo,hi,elo,ehi
