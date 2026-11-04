import numpy as np
from scipy.integrate import quad
w3,w5=2**-0.75,2**-1.25
def J(w,m,k): return quad(lambda v:2/np.sqrt(m+k*v*v+(1-m-k)*v**6),w,1,epsabs=1e-13,epsrel=1e-13)[0]
def ratio(m,k):
    J3,J5=J(w3,m,k),J(w5,m,k)
    if k<0:
        s=np.sqrt(-k); return 2*np.sin(s*J5)/np.sin(s*J3)
    if k>0:
        s=np.sqrt(k); return 2*np.sinh(s*J5)/np.sinh(s*J3)
    return 2*J5/J3
def lower(m,k): # certified-style lower bound with sin x >= x - x^3/4, sin<=x
    J3,J5=J(w3,m,k),J(w5,m,k)
    return 2*(J5-(-k)*J5**3/4)/J3
for k in [0,-0.05,-0.1,-0.12,-0.15]:
    ms=np.linspace(max(0.1,-k),1,46)
    r=min((ratio(m,k),m) for m in ms); lb=min((lower(m,k),m) for m in ms)
    print(k,'min ratio %.4f at %.2f'%r,' lowerbound %.4f at %.2f'%lb, 'J5 range',min(J(w5,m,k) for m in ms),max(J(w5,m,k) for m in ms))
