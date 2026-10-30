import numpy as np
Om,w0,wa=0.245,-0.93,-0.41
Ob=1-Om
q0=0.5+1.5*Ob*w0
j0=1+1.5*Ob*(3*w0*(1+w0)+wa)
s0=-3.5-33/4*Ob*wa-9/4*Ob*(9+(7-Om)*wa)*w0-9/4*Ob*(16-3*Om)*w0**2-27/4*Ob*(3-Om)*w0**3
s0plus=s0+2*27/4*Ob*(3-Om)*w0**3
def l0(c): return 35/2+Ob/4*(213+c*(7-Om)*wa)*wa+Ob/4*(489+9*(82-21*Om)*wa)*w0+4.5*Ob*(67-21*Om+1.5*(23-11*Om)*wa)*w0**2+27/4*Ob*(47-24*Om)*w0**3+81/2*Ob*(3-2*Om)*w0**4
print('q0,j0,s0,s0(+typo)',q0,j0,s0,s0plus)
print('l0 true',l0(9),'printed',l0(1),'diff',l0(9)-l0(1))
E=lambda z: np.sqrt(Om*(1+z)**3+Ob*(1+z)**(3*(1+w0+wa))*np.exp(-3*wa*z/(1+z)))
def Hser(z,n,s=s0,l=None):
    c=[1,1+q0,(-q0**2+j0)/2,(3*q0**2+3*q0**3-4*q0*j0-3*j0-s)/6,
       (-12*q0**2-24*q0**3-15*q0**4+32*q0*j0+25*q0**2*j0+7*q0*s+12*j0-4*j0**2+8*s+(l if l is not None else 0))/24]
    return sum(c[k]*z**k for k in range(n+1))
for z in [0.5,1.0,1.5,1.8,2.0]:
    r=lambda h: abs(E(z)-h)/E(z)
    print(z,'2p %.3f 3p %.3f 4p_true %.3f 4p_printed %.3f 3p(s+) %.3f'%(r(Hser(z,2)),r(Hser(z,3)),r(Hser(z,4,l=l0(9))),r(Hser(z,4,l=l0(1))),r(Hser(z,3,s=s0plus))))
print('---fine')
zs=np.linspace(0.05,2,40)
for z in zs:
    r=lambda h: abs(E(z)-h)/E(z)
    print('%.2f 2p %.3f 3p %.3f 4pT %.3f 4pP %.3f'%(z,r(Hser(z,2)),r(Hser(z,3)),r(Hser(z,4,l=l0(9))),r(Hser(z,4,l=l0(1)))))
