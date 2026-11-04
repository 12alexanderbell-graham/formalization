import numpy as np
from scipy.integrate import quad
l=np.log(10)
def DL(z,Om): return (1+z)*quad(lambda t:1/np.sqrt(Om*(1+t)**3+1-Om),0,z,epsabs=1e-13,epsrel=1e-13)[0]
def T4(z,Om):
    x=np.log10(1+z)
    a2=l*(1.5-0.75*Om); a3=l**2*(9/8*Om**2-2*Om+7/6); a4=l**3*(-135/64*Om**3+18/4*Om**2-47/16*Om+5/8)
    return l*(x+a2*x**2+a3*x**3+a4*x**4)
def T3(z,Om):
    x=np.log10(1+z)
    a2=l*(1.5-0.75*Om); a3=l**2*(9/8*Om**2-2*Om+7/6)
    return l*(x+a2*x**2+a3*x**3)
for Om in [0.25,0.3,0.35]:
  for z in [1,2,3,4,5,5.1,6,6.7,7]:
    d=DL(z,Om); print(Om,z,'T4 rel %.4f'%(T4(z,Om)/d-1),'T3 rel %.4f'%(T3(z,Om)/d-1))
