import mpmath as mp
from taylor import *
mp.mp.dps=40
c=mp.sqrt(mp.mpf('0.1')); a=mp.mpf('1.0096196291173984457979707684536')
f=mp.mpf(0);p=mp.mpf(0);q=a;s=mp.mpf(0);h=mp.mpf(1)/64
while True:
    F,P,Q=taylor_step(f,p,q,10,h,30)
    if ev(P,h)>mp.mpf('0.9999'):
        lo,hi=mp.mpf(0),h
        for _ in range(100):
            m=(lo+hi)/2
            if ev(P,m)>mp.mpf('0.9999'): hi=m
            else: lo=m
        print('upper: p=0.9999 at s=%s eta=%s, unscaled f\'\'=%s'%(mp.nstr(s+hi,6),mp.nstr((s+hi)/c,6),mp.nstr(c*ev(Q,hi),4)))
        break
    f,p,q=ev(F,h),ev(P,h),ev(Q,h); s+=h
