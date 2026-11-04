import numpy as np
from scipy.integrate import quad
w3,w5=2**-0.75,2**-1.25
def ratio(m,k):
    ys=[m+k*v*v+(1-m-k)*v**6 for v in np.linspace(w5,1,300)]
    if min(ys)<=0: return None
    J=lambda w: quad(lambda v:2/np.sqrt(m+k*v*v+(1-m-k)*v**6),w,1,limit=200)[0]
    J3,J5=J(w3),J(w5); s=np.sqrt(-k)
    if s*J3>=np.pi: return None
    return 2*np.sin(s*J5)/np.sin(s*J3)
for k in np.arange(-0.12,-0.40,-0.02):
    vals=[(ratio(m,k),m) for m in np.linspace(0.1,1,91)]
    vals=[v for v in vals if v[0] is not None]
    print('%.2f'%k,'min %.4f at m=%.2f'%min(vals))
