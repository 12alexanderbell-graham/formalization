import mpmath as mp
from taylor import *
mp.mp.dps=30
for a in ['-0.4444461497','-0.4444461493']:
    f=mp.mpf(0);p=mp.mpf(0);q=mp.mpf(a);s=mp.mpf(0);h=mp.mpf(1)/64
    pmin=(1,0);pmax_dip=-1;fmin=(1,0);qmax=0; pz=None; tau=None
    while s<4:
        F,P,Q=taylor_step(f,p,q,10,h,25)
        for j in range(1,33):
            x=h*j/32; pv=ev(P,x); fv=ev(F,x); qv=ev(Q,x)
            if pv<pmin[0]: pmin=(pv,s+x)
            if s+x<=0.75: pmax_dip=max(pmax_dip,pv)
            if fv<fmin[0]: fmin=(fv,s+x)
            qmax=max(qmax,abs(qv))
            if tau is None and qv>0: tau=s+x
            if pz is None and s+x>0.01 and pv>0: pz=s+x
        f,p,q=ev(F,h),ev(P,h),ev(Q,h); s+=h
    print(a,'min p=%s at s=%s; max p on (0,3/4]=%s; q zero tau~%s; p returns to 0 at s~%s; min F=%s at %s; max|Q|=%s'%(mp.nstr(pmin[0],6),mp.nstr(pmin[1],4),mp.nstr(pmax_dip,4),mp.nstr(tau,4),mp.nstr(pz,4),mp.nstr(fmin[0],6),mp.nstr(fmin[1],4),mp.nstr(qmax,4)))
