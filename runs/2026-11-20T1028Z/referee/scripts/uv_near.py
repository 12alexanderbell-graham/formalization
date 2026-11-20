import sys
sys.argv=['x','40','0.01']
exec(open('gel_dec.py').read().split("roots=[]")[0])
prev=None
while s<4540:
    h=FR*s
    Wc,pc=taylor(s,W,p)
    for i in range(5):
        t=h*i/5; ss=s+t; pp=ev(pc,t); WW=ev(Wc,t); v=-ss*pp; u=ss*WW.exp()/(-pp)
        if ss>4000 and (prev is not None) and ((prev[1]-1)*(u-1)<0):
            print('u=1 crossing near',f"{ss:.2f}",'v=',f"{v:.8f}")
        if ss>4000 and abs(ss-4380)<1.5 or abs(ss-4532)<1: print(f"{ss:.2f} u={u:.6f} v={v:.8f}")
        prev=(ss,u,v)
    W=ev(Wc,h); p=ev(pc,h); s+=h
