import mpmath as mp
from townes_float import series
mp.mp.dps=30
c=mp.mpf('2.2062008646')
r0=mp.mpf(1)/20
Q0,P0=series(c,r0)
f=mp.odefun(lambda r,y:[y[1],-y[1]/r+y[0]-y[0]**3],r0,[Q0,P0])
import math
tot=0; r=r0; h=0.05
for R in [0.5,1,2,3,4,6,8,10,12]:
    while r<R:
        Q,P=f(r+h/2)
        TH=abs(Q)+0.01
        K=max(1,1/r+max(1,3*TH**2-1))
        tot+=K*h*(1+K*h/2); r+=h
    print(R, float(tot), float(f(R)[0]), float(f(R)[1]))
