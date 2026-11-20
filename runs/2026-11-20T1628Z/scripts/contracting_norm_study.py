# Float study: log-norm of the homology Jacobian along the regular isothermal solution in a quadratic norm.
import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import solve_continuous_lyapunov
# regular solution: w'' + 2/s w' + e^w = 0, w(0)=0; series start
def f(s,y):
    w,p=y
    return [p, -2/s*p-np.exp(w)]
s0=1e-3; w0=-s0**2/6+s0**4/120; p0=-s0/3+s0**3/30
sol=solve_ivp(f,[s0,7e4],[w0,p0],method='DOP853',rtol=1e-13,atol=1e-15,dense_output=True)
J0=np.array([[-1.,-1.],[2.,0.]])
# P with J0^T P + P J0 = -I
P=solve_continuous_lyapunov(J0.T,-np.eye(2))
print('P',P)
L=np.linalg.cholesky(P); R=L.T; Ri=np.linalg.inv(R)
def mu(J):  # log norm in ||x||_P = |R x|
    A=R@J@Ri; S=(A+A.T)/2; return np.linalg.eigvalsh(S).max()
print('mu at eq', mu(J0))
ts=np.geomspace(1,7e4,4000)
ws,ps=sol.sol(ts)
u=ts*np.exp(ws)/(-ps); v=-ts*ps
lam=ts**2*np.exp(ws)
mus=[]
for a,b in zip(u,v):
    J=np.array([[3-2*a-b,-a],[b,a-1]]); mus.append(mu(J))
mus=np.array(mus)
for T in [5,10,20,50,100,200,429,1000,4700,10000,48978,70000]:
    i=np.searchsorted(ts,T)
    print(f"t={ts[i]:9.1f} u={u[i]:.5f} v={v[i]:.5f} lam={lam[i]:.6f} mu_P={mus[i]:+.4f}  max mu_P on [t,end]={mus[i:].max():+.4f}")
# turning points: v=2 crossings
cr=[ts[i] for i in range(len(ts)-1) if (v[i]-2)*(v[i+1]-2)<0]
print('v=2 crossings ~', [round(c,1) for c in cr[:8]])
