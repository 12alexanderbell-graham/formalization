# Algebraic tails: stiff (Radau) integration, unscaled alpha=0.3,0.31,0.319 at beta=-0.1; eta*r -> 2|beta|=0.2
import numpy as np
from scipy.integrate import solve_ivp
K=10.0; c=np.sqrt(0.1)
def rhs(s,y): f,p,q=y; return [p,q,-K*f*q+1-p*p]
for a_un in [0.3,0.31,0.319]:
    a=a_un/c
    sol=solve_ivp(rhs,[0,400*c],[0,0,a],method='Radau',rtol=1e-12,atol=1e-15,dense_output=True)
    for eta in [31.6,100,200,400]:
        f,p,q=sol.sol(eta*c); print('alpha_un=%.3f eta=%6.1f  p=%.8f  1-p=%.3e  eta*r_unscaled=%.4f'%(a_un,eta,p,1-p,eta*(q*c)/(1-p)))
