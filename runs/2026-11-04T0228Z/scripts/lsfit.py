import numpy as np
from scipy.optimize import least_squares
from explore import D, T, zs, feas
def mu_res(a, Om, zgrid, Dg):
    x=np.log10(1+zgrid); P=x+a[0]*x**2+a[1]*x**3
    return 5*np.log10(np.abs(P)/Dg)
def fit(Om, zmax, weight):
    zg=np.linspace(0.01,zmax,300) if weight=='z' else np.expm1(np.linspace(np.log(1.01),np.log(1+zmax),300))
    Dg=np.array([D(Om,z) for z in zg])
    f=lambda p: mu_res(p[:2],Om,zg,Dg)-p[2]
    r=least_squares(f,[*T(Om),0.0])
    return r.x[:2]
def halfrange(a,Om):
    z=np.array(zs); r=mu_res(a,Om,z,np.array([D(Om,zz) for zz in z])); return (r.max()-r.min())/2
for Om in [0.1,0.3,0.6,1.0]:
    for zmax in [4.66,5.1]:
        for w in ['z','lnz']:
            a=fit(Om,zmax,w); s=0.2
            print(f"Om={Om} zmax={zmax} w={w}: fit=({a[0]:.3f},{a[1]:.3f}) halfrange5={halfrange(a,Om):.4f} ell-ellT={(a[1]-s*a[0])-(T(Om)[1]-s*T(Om)[0]):.3f}")
    print(f"  Taylor halfrange5={halfrange(T(Om),Om):.4f}")
