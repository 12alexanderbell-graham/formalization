import numpy as np
from scipy.integrate import quad
L10=np.log(10)
def DL(z,Om):
    return (1+z)*quad(lambda t:1/np.sqrt(Om*(1+t)**3+1-Om),0,z,epsabs=1e-13,epsrel=1e-13)[0]
def P(x,a):
    return x+sum(ai*x**(i+2) for i,ai in enumerate(a))
samples={'SQG':(3.205,3.564,-2.510),'SQ':(3.075,4.466,-3.716),'SG':(3.304,2.069,2.571)}
def spread(a,Om,zs):
    r=[5*np.log10(DL(z,Om))-5*np.log10(L10*P(np.log10(1+z),a)) for z in zs]
    return (max(r)-min(r))/2
for zs_name,zs in [('q3',[2**.5-1,2**1.5-1,2**2.5-1]),('q4',[2**.5-1,2**1.5-1,2**2.5-1,7]),('dense',list(np.linspace(0.05,7,60))),('dense5',list(np.linspace(0.05,5,60)))]:
  for k,a in samples.items():
    best=min((spread(a,Om,zs),Om) for Om in np.linspace(0,1,101))
    print(zs_name,k,'min half-spread %.4f at Om %.2f'%best)
print('---- extended Om')
zs=[2**.5-1,2**1.5-1,2**2.5-1]
for k,a in samples.items():
    vals=[(spread(a,Om,zs),Om) for Om in np.linspace(0,4,201)]
    print(k,'min %.4f at Om %.2f'%min(vals), ' at Om=1: %.4f'%spread(a,1,zs), ' Om=0.3: %.4f'%spread(a,0.3,zs))
# with only 2 points
for pts in [[2**.5-1,2**2.5-1],[2**1.5-1,2**2.5-1],[2**.5-1,2**1.5-1]]:
  for k,a in samples.items():
    print(pts, k, '%.4f at %.2f'%min((spread(a,Om,pts),Om) for Om in np.linspace(0,1,101)))
