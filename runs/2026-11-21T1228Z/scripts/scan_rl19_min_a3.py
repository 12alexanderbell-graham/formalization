# Float scan (unchecked): minimum a3 of cubics matching exact flat LCDM within 0.05 mag (common offset) at 1+z = sqrt2, 2sqrt2, 4sqrt2
import mpmath as mp
from scipy.optimize import linprog
l=float(mp.log(2)); L=float(mp.log(10))
us=[l/2,3*l/2,5*l/2]; S=[2**.5,2*2**.5,4*2**.5]; k=10**0.01
worst=(9,None)
for i in range(0,101):
  O=i/100
  J=lambda w: float(mp.quad(lambda v:2/mp.sqrt(O+(1-O)*v**6),[w,1]))
  D=[S[j]*J(1/S[j]**.5) for j in range(3)]
  A=[];b=[]
  for j in range(3):
    u=us[j]; A.append([-u*u,-u**3, D[j]/k]); b.append(u); A.append([u*u,u**3,-D[j]*k]); b.append(-u)
  r=linprog([0,1,0],A_ub=A,b_ub=b,bounds=[(None,None),(None,None),(0,None)])
  a3=r.x[1]*L*L
  if a3<worst[0]: worst=(a3,O,r.x[0]*L)
print('min over Omega in [0,1] of min a3:',worst)
