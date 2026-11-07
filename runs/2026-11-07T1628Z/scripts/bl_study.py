import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import expm, eigh, cholesky
def F(t,y):
    g,p,q=y[:3]; Phi=y[3:].reshape(3,3)
    J=np.array([[0,1,0],[0,0,1],[-q/2,0,-g/2]])
    return np.concatenate([[p,q,-g*q/2],(J@Phi).ravel()])
T=9.0
sol=solve_ivp(F,[0,T],np.concatenate([[0,0,1],np.eye(3).ravel()]),rtol=1e-11,atol=1e-13,dense_output=True)
ts=np.linspace(0,T,181)
Y=sol.sol(ts)
print("fundamental matrix norm at T:", np.linalg.norm(Y[3:,-1].reshape(3,3),2))
# Lipschitz bound amplification: K=(|g|+|q|)/2 per the cell rule, but K>=1 too: K = max(1,(GH+QH)/2) roughly
K=np.maximum(1,(np.abs(Y[0])+np.abs(Y[2]))/2+1)  # plus J's off-diagonal 1s
print("Lipschitz amplification exp(int K):", np.exp(np.trapezoid(K,ts)))
# one-sided with constant quadratic weight W=L^T L, L=diag(a,b,1) scaled; mu(t)= lambda_max of sym(L J L^-1)
def mu(W_L, g,q):
    J=np.array([[0,1,0],[0,0,1],[-q/2,0,-g/2]])
    A=W_L@J@np.linalg.inv(W_L)
    return np.linalg.eigvalsh((A+A.T)/2).max()
best=None
for a in np.logspace(-3,1,41):
  for b in np.logspace(-3,1,41):
    Lm=np.diag([a,b,1.0])
    m=[mu(Lm,Y[0,i],Y[2,i]) for i in range(len(ts))]
    amp=np.exp(np.trapezoid(m,ts))
    if best is None or amp<best[0]: best=(amp,a,b)
print("best constant diagonal weight amplification:",best)
# piecewise: per segment of length 1 choose best diagonal weight, change cost = cond ratio
segs=np.arange(0,T+1e-9,1.0)
tot=0;prev=None;cost=1
for s0,s1 in zip(segs[:-1],segs[1:]):
    idx=(ts>=s0)&(ts<=s1)
    bb=None
    for a in np.logspace(-3,2,51):
      for b in np.logspace(-3,2,51):
        Lm=np.diag([a,b,1.0])
        m=[mu(Lm,Y[0,i],Y[2,i]) for i in np.where(idx)[0]]
        v=np.trapezoid(m,ts[idx])
        if bb is None or v<bb[0]: bb=(v,a,b)
    tot+=bb[0]
    if prev is not None:
        r=np.array([bb[1]/prev[1],bb[2]/prev[2],1.0]); cost*=r.max()/r.min()
    prev=bb
    print(f"[{s0},{s1}] int mu={bb[0]:.3f} a={bb[1]:.3g} b={bb[2]:.3g} g={Y[0,idx].max():.2f}")
print("piecewise amplification", np.exp(tot), "weight-change cost", cost)
