import sys
sys.argv=['x','40','0.01']
src=open('gel_dec.py').read().split("roots=[]")[0]
exec(src)
umin=umax=None; vmin_mid=None; v4380=v4700=None; uall=[]; vm=None
while s<4700.5:
    h=FR*s
    Wc,pc=taylor(s,W,p)
    for i in range(0,5):
        t=h*i/5; ss=s+t; pp=ev(pc,t); WW=ev(Wc,t)
        v=-ss*pp; u=ss*WW.exp()/(-pp)
        if 428.95<=ss<=4380 : vm=v if vm is None else min(vm,v)
        if 4380<=ss<=4700:
            umin=u if umin is None else min(umin,u); umax=u if umax is None else max(umax,u)
        if v4380 is None and ss>=4380: v4380=(ss,v)
        if v4700 is None and ss>=4700: v4700=(ss,v)
    W=ev(Wc,h); p=ev(pc,h); s+=h
print('min v on [428.95,4380]',f"{vm:.10f}")
print('u on [4380,4700] min',f"{umin:.10f}",'max',f"{umax:.10f}")
print('v(4380)',v4380[0],f"{v4380[1]:.10f}",'v(4700)',v4700[0],f"{v4700[1]:.10f}")
