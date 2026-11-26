# Run 2026-11-26T0628Z: the reversed-flow solution of row beta=-5/100 in the scaled variables of RFiveTube
# (K = 20, Q' = -K F Q + 1 - P^2, Q(0) = alpha in the tube's window): where is F < 0 with Q > 0, where does F
# return to zero, and how large is Q on the window up to L = 7/4?
import numpy as np
from scipy.integrate import solve_ivp
K=20.0; a=-193681201768179/400000000000000
sol=solve_ivp(lambda t,y:[y[1],y[2],-K*y[0]*y[2]+1-y[1]**2],(0,1.75),[0,0,a],rtol=1e-12,atol=1e-14,max_step=1/1024)
t=sol.t; F,P,Q=sol.y
for tt in np.arange(0.5,1.76,1/16):
    i=np.argmin(abs(t-tt)); print(f"t={t[i]:.4f} F={F[i]:+.5f} P={P[i]:+.5f} Q={Q[i]:+.5f}")
iq=np.where((Q[:-1]<=0)&(Q[1:]>0))[0]; i0=np.where((F[:-1]<0)&(F[1:]>=0)&(t[:-1]>0.01))[0]
print("Q crosses 0 at t =",t[iq], " F returns to 0 at t =",t[i0], " Q there:",Q[i0], " max Q on [Q>0,L]:",Q[iq[0]+1:].max())
