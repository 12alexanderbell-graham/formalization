from mpmath import mp, mpf, sqrt, log10, log
mp.dps=20
lam=log10(2); xs=[lam/2, 3*lam/2, 5*lam/2]; Z=[sqrt(2),2*sqrt(2),4*sqrt(2)]
L10=log(10); k=mpf(20)/3*lam
def B(a2,a3,x): return x+a2*x**2+a3*x**3
dS=[z*(z-1) for z in Z]
EdS=[2*z*(1-1/sqrt(z)) for z in Z]
for name,d in [('dS',dS),('EdS',EdS)]:
  for a2 in [3.43,3.49]:
    for a3 in [1.57,1.69]:
      r=[5*log10(d[i]/B(a2,a3,xs[i])) for i in range(3)]
      print(name,a2,a3,[round(float(x),4) for x in r], 'r1-r3',round(float(r[0]-r[1]),3),'r3-r5',round(float(r[1]-r[2]),3),'r1-r5',round(float(r[0]-r[2]),3))
