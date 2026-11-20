# Float prototype of a contracting-cell chain (no rigour): radius in the P-norm, log-norm bound per cell
# from the 4 corners of the cell's (u, v) box (mu_P(J) is convex in J and J is affine in (u, v)).
import numpy as np
from scipy.integrate import solve_ivp
P=np.array([[1.5,.5],[.5,1.]]); R=np.linalg.cholesky(P).T; Ri=np.linalg.inv(R)
def mu(a,b):
    J=np.array([[3-2*a-b,-a],[b,a-1]]); A=R@J@Ri; return np.linalg.eigvalsh((A+A.T)/2).max()
# P-norm of a max-norm box of half-width r: <= sqrt(lmax(P))*sqrt(2)*r ; max-norm from P-norm: <= r/sqrt(lmin(P))
lmax,lmin=np.linalg.eigvalsh(P)[::-1]
def f(s,y): w,p=y; return [p,-2/s*p-np.exp(w)]
s0=1e-3; sol=solve_ivp(f,[s0,6e4],[-s0**2/6,-s0/3],method='DOP853',rtol=1e-13,atol=1e-15,dense_output=True)
def uv(t):
    w,p=sol.sol(t); return t*np.exp(w)/(-p), -t*p
for dtau,defect in [(0.05,1e-13),(0.1,1e-13),(0.2,1e-12)]:
    t=100.; rP=5e-6*np.sqrt(2*lmax); n=0; worst=-9
    while t<5e4:
        t1=t*np.exp(dtau); ts=np.geomspace(t,t1,9); U,V=uv(ts)
        rmax=rP/np.sqrt(lmin)
        corners=[(U.min()-rmax,V.min()-rmax),(U.min()-rmax,V.max()+rmax),(U.max()+rmax,V.min()-rmax),(U.max()+rmax,V.max()+rmax)]
        m=max(mu(a,b) for a,b in corners); worst=max(worst,m)
        rP=np.exp(m*dtau)*rP+defect*dtau; t=t1; n+=1
    print(f"dtau={dtau}: cells={n}, worst corner mu={worst:+.3f}, final radius (max norm) ~ {rP/np.sqrt(lmin):.2e}")
