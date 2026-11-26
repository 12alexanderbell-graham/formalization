# Run 2026-11-26T0628Z: hypothesis 6 at beta = -19/200 (K = 200/19), scaled variables: reversed solution from
# A_rev, where Q > 0, F < 0, where F returns to zero and Q there, against the attached A_att.
import numpy as np
from scipy.integrate import solve_ivp
K=200/19; Arev=-0.4510136279431539; Aatt=1.064501932279109
sol=solve_ivp(lambda t,y:[y[1],y[2],-K*y[0]*y[2]+1-y[1]**2],(0,1.5),[0,0,Arev],rtol=1e-13,atol=1e-15,max_step=1/2048,method='DOP853')
t=sol.t; F,P,Q=sol.y
for tt in np.arange(0.375,1.51,1/32):
    i=np.argmin(abs(t-tt)); print(f"t={t[i]:.5f} F={F[i]:+.5f} P={P[i]:+.5f} Q={Q[i]:+.5f}")
iq=np.where((Q[:-1]<=0)&(Q[1:]>0))[0]; i0=np.where((F[:-1]<0)&(F[1:]>=0)&(t[:-1]>0.01))[0]
print("Q>0 from t =",t[iq], " F=0 at t* =",t[i0]," Q(t*) =",Q[i0]," A_att =",Aatt, " Q(1.5) =",Q[-1], "F(1.5)=",F[-1], "P(1.5)=",P[-1])
