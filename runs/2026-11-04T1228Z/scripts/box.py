import numpy as np, itertools
from scipy.integrate import quad
L10=np.log(10)
def DL(z,Om): return (1+z)*quad(lambda t:1/np.sqrt(Om*(1+t)**3+1-Om),0,z,epsabs=1e-13,epsrel=1e-13)[0]
def P(x,a): return x+a[0]*x**2+a[1]*x**3+a[2]*x**4
tab={'SQG':[(3.205,.165,.162),(3.564,.916,.938),(-2.510,1.595,1.536)],
     'SQ':[(3.075,.172,.169),(4.466,1.013,1.040),(-3.716,1.922,1.852)],
     'SG':[(3.304,.186,.183),(2.069,1.1217,1.252),(2.571,2.631,2.506)]}
z3,z5=2**1.5-1,2**2.5-1; x3,x5=np.log10(1+z3),np.log10(1+z5)
Oms=np.linspace(0,1,201)
R=np.array([DL(z5,O)/DL(z3,O) for O in Oms])
print('R range',R.min(),R.max())
for k,t in tab.items():
  for s in [0,0.25,0.5,0.75,1.0]:
    rs=[]
    for signs in itertools.product([0,1],repeat=3):
        a=[c+(up if sg else -dn)*s for (c,up,dn),sg in zip(t,signs)]
        p3,p5=P(x3,a),P(x5,a)
        rs.append(p5/p3 if p3>0 else np.nan)
    rs=np.array(rs)
    # spread in mag = 5*log10(ratio_true/ratio_poly) ; matched within tol tau (each within tau of c) iff |5log10(R/r)|<=2tau
    if np.isnan(rs).any(): print(k,s,'P3<=0'); continue
    lo,hi=rs.min(),rs.max()
    # min over Omega of distance of R to [lo,hi] in mag
    d=[0 if lo<=r<=hi else 5*min(abs(np.log10(r/lo)),abs(np.log10(r/hi))) for r in R]
    print(k,'s=%.2f'%s,'poly ratio [%.4f,%.4f]'%(lo,hi),'min full spread mag %.4f'%min(d))
