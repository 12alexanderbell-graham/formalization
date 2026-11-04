# Numerical exploration (floating point, not evidence): minimax-type feasibility of the
# RL19 cubic log-polynomial against exact flat LCDM at redshifts 1+z = 2^(k/2).
import numpy as np, mpmath as mp
from scipy.optimize import linprog
mp.mp.dps = 30
L10 = float(mp.log(10))
def D(Om, z):  # H0 d_L, c = 1
    w = (1+z)**-0.5
    return float((1+z)*mp.quad(lambda v: 2/mp.sqrt(Om+(1-Om)*v**6), [w, 1]))
def T(Om): return np.array([L10*(1.5-0.75*Om), L10**2*(9/8*Om**2-2*Om+7/6)])
def feas(Om, zs, eps, n):
    xs = [np.log10(1+z) for z in zs]; Ds = [D(Om,z) for z in zs]
    A=[];b=[]
    f = 10**(2*eps/5)
    for j in range(len(zs)):
        A.append([-xs[j]**2, -xs[j]**3]); b.append(xs[j]-1e-9)  # P_j > 0
        for k in range(len(zs)):
            if j==k: continue
            rho = f*Ds[k]/Ds[j]
            # P_k - rho P_j <= 0
            A.append([xs[k]**2-rho*xs[j]**2, xs[k]**3-rho*xs[j]**3]); b.append(-(xs[k]-rho*xs[j]))
    res = linprog(c=n, A_ub=A, b_ub=b, bounds=[(None,None)]*2)
    return res
zs = [2**(k/2)-1 for k in range(1,6)]
if __name__=="__main__":
  print("redshifts", [round(z,3) for z in zs])
  RL = np.array([3.45,1.6])
  for eps in [0.05, 0.1, 0.15]:
    print("eps",eps)
    for Om in [0.05,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,1.0]:
      t=T(Om)
      out=[]
      for n in [np.array([-1.,0]),np.array([1.,0]),np.array([0,-1.]),np.array([0,1.])]:
          r=feas(Om,zs,eps,n)
          out.append(None if r.status!=0 else round(r.fun,3))
      # a2 in [-out1? ] ranges
      a2r = (out[0] and -out[0], out[1]); a3r=(out[2] and -out[2], out[3])
      print(f" Om={Om:.2f} T=({t[0]:.3f},{t[1]:.3f}) a2 in [{out[1]},{-out[0] if out[0] is not None else None}] a3 in [{out[3]},{-out[2] if out[2] is not None else None}]")
  