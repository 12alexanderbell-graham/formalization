import numpy as np
from scipy.integrate import solve_ivp
s0=1e-4; w=-s0**2/6+s0**4/120; wp=-s0/3+4*s0**3/120
y0=[s0*np.exp(w)/(-wp), -s0*wp]
ev=lambda t,y:2*y[0]-y[1]
sol=solve_ivp(lambda t,y:[y[0]*(3-y[0]-y[1]),y[1]*(y[0]-1)],[np.log(s0),33],y0,method='DOP853',rtol=1e-13,atol=1e-30,events=ev)
c=np.sqrt(2/np.pi)
for t,y in zip(sol.t_events[0],sol.y_events[0]): print('%.15e %.12e'%(np.exp(t),np.sqrt(y[0]*y[1]**3/4/np.pi)-c))
