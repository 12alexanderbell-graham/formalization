import mpmath as mp
mp.mp.dps=30
for a,s in [('0.5','1.28125'),('1.009619629','3.0'),('-0.4444461493','4.0')]:
    sol=mp.odefun(lambda t,y:[y[1],y[2],-10*y[0]*y[2]+1-y[1]**2],0,[mp.mpf(0),mp.mpf(0),mp.mpf(a)])
    f,p,q=sol(mp.mpf(s)); print('odefun alpha=%s s=%s: 1-P=%s Q=%s F=%s'%(a,s,mp.nstr(1-p,6),mp.nstr(q,6),mp.nstr(f,8)))
