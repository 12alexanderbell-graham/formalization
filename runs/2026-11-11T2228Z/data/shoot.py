import sys
from scipy.integrate import solve_ivp
K=float(sys.argv[1]); beta=float(sys.argv[2])
def cls(S,a):
    f=lambda t,y:[y[1],y[2],-K*y[0]*y[2]-beta*(1-y[1]**2)]
    e1=lambda t,y:y[2]; e1.terminal=True; e1.direction=-1
    e2=lambda t,y:y[1]-1; e2.terminal=True; e2.direction=1
    s=solve_ivp(f,[0,40],[S,0,a],rtol=1e-11,atol=1e-13,events=[e1,e2])
    if len(s.t_events[0]): return -1,s.t_events[0][0]
    if len(s.t_events[1]): return 1,s.t_events[1][0]
    return 0,None
for S in map(float,sys.argv[3:]):
    lo,hi=0.01,5.0
    for _ in range(45):
        m=(lo+hi)/2
        if cls(S,m)[0]<0: lo=m
        else: hi=m
    print(S, lo, cls(S,lo*0.97), cls(S,lo*1.03))
