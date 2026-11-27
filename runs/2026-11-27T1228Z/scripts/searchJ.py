# Search for F(R) models with matter where the jerk combination J = j - q - 2 can vanish (run 2026-11-27T1228Z,
# eta_ratios hypothesis 4). Scale factor with (a0/a)^3 = P(t) a polynomial: H = -P'/(3P), rho = c P.
# phi(t) = G(R(t)) with G quadratic; the master equation phi'' - H phi' + 2 H' phi + rho = 0 must hold identically.
import sympy as sp, itertools
t=sp.symbols('t')
def run(deg):
    ps=sp.symbols('p1:%d'%(deg+1)); g0,g1,g2,c=sp.symbols('g0 g1 g2 c')
    P=1+sum(ps[i]*t**(i+1) for i in range(deg))
    H=-sp.diff(P,t)/(3*P)
    R=sp.together(-6*(sp.diff(H,t)+2*H**2))
    G=g0+g1*R+g2*R**2
    phi=G
    expr=sp.diff(phi,t,2)-H*sp.diff(phi,t)+2*sp.diff(H,t)*phi+c*P
    num=sp.numer(sp.together(expr))
    eqs=sp.Poly(sp.expand(num),t).coeffs()
    sol=sp.solve(eqs,list(ps)+[g0,g1,g2,c],dict=True)
    return P,H,R,sol
for deg in (1,2,3):
    P,H,R,sol=run(deg)
    print('deg',deg)
    for s in sol:
        print('  ',s)
