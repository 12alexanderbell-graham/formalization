import mpmath as mp
from taylor import *
mp.mp.dps=50
h=mp.mpf(1)/32
def table(a, nodes):
    K=10; mu=3; th=mp.mpf(11)/30
    f=mp.mpf(0); p=mp.mpf(0); q=mp.mpf(a); s=mp.mpf(0); rows=[]
    pk=(mp.mpf(-10),None)
    while s<max(nodes)+1e-9:
        F,P,Q=taylor_step(f,p,q,K,h,30)
        for j in range(1,65):
            x=h*j/64; v=ev(P,x)
            if v>pk[0]: pk=(v,s+x)
        f,p,q=ev(F,h),ev(P,h),ev(Q,h); s+=h
        for n in nodes:
            if abs(s-n)<1e-9: rows.append((n,p,q,f))
    print('alpha =',a,'  max p on [0,%s] = %s at s=%s'%(max(nodes),mp.nstr(pk[0]-1,4)+' (p-1)',mp.nstr(pk[1],5)))
    for n,p,q,f in rows:
        print('  s=%-7s P=%s 1-P=%s Q=%s 3(1-P)-Q=%s F=%s F-th=%s'%(mp.nstr(n,5),mp.nstr(p,8),mp.nstr(1-p,3),mp.nstr(q,3),mp.nstr(3*(1-p)-q,3),mp.nstr(f,5),mp.nstr(f-th,3)))
table('0',[1.375,1.625])
table('0.5',[1.03125,1.28125])
table('1',[1.46875,1.71875])
table('1.009619629',[2.5,2.625,2.75,3.0,3.25])
table('1.0096196292',[2.5,2.5625,2.75,2.78125,3.0])
table('-0.4444461497',[0.75,3.5,3.75,4.0])
table('-0.4444461493',[0.75,3.625,3.75,4.0])
table('0.25',[1.1875,1.4375])
table('0.75',[0.90625,1.15625,1.25])
