import numpy as np
from scipy.integrate import quad
def DL(z,Om): return (1+z)*quad(lambda t:1/np.sqrt(Om*(1+t)**3+1-Om),0,z,epsabs=1e-14,epsrel=1e-14)[0]
z3,z5=2**1.5-1,2**2.5-1; L=np.log10(2); x3,x5=1.5*L,2.5*L
P=lambda x,a:x+a[0]*x**2+a[1]*x**3+a[2]*x**4
Rmin=min(DL(z5,O)/DL(z3,O) for O in np.linspace(0,1,1001)); print('Rmin',Rmin, DL(z5,1)/DL(z3,1))
for k,t in {'SQG':[(3.205,.165,.162),(3.564,.916,.938),(-2.510,1.595,1.536)],'SQ':[(3.075,.172,.169),(4.466,1.013,1.040),(-3.716,1.922,1.852)]}.items():
  for s in np.arange(0.9,1.5,0.02):
    a=[t[0][0]-s*t[0][2],t[1][0]+s*t[1][1],t[2][0]+s*t[2][1]]
    r=P(x5,a)/P(x3,a)
    if r>=Rmin: print(k,'s_max ~ %.2f'%s); break
  a=[t[0][0]-t[0][2],t[1][0]+t[1][1],t[2][0]+t[2][1]]; print(k,'corner',a,'ratio',P(x5,a)/P(x3,a), 'center ratio', P(x5,[c[0] for c in t])/P(x3,[c[0] for c in t]))
print('R(1/3)',DL(z5,1/3)/DL(z3,1/3),'SG center',P(x5,[3.304,2.069,2.571])/P(x3,[3.304,2.069,2.571]))
