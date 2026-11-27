# hJ search in the expansion-rate variable (run 2026-11-27T1228Z): H' = f(H), R(H) = R0 + k (H - 1)^2 has an
# extremum at H0 = 1 (so the curvature's time derivative vanishes today), f = -R/6 - 2 H^2, vacuum,
# phi = G(R(H)), G = 1 + g1 (R - R0) + g2 (R - R0)^2 + g4 (R - R0)^4 (G''' = 0 at R0).
# Master equation in H: f Phi'' + (f' - H) Phi' + 2 Phi = 0 identically.
import sympy as sp
H,R0,k,g1,g2,g4=sp.symbols('H R0 k g1 g2 g4')
R=R0+k*(H-1)**2
f=-R/6-2*H**2
G=1+g1*(R-R0)+g2*(R-R0)**2+g4*(R-R0)**4
Phi=G
e=sp.expand(f*sp.diff(Phi,H,2)+(sp.diff(f,H)-H)*sp.diff(Phi,H)+2*Phi)
eqs=sp.Poly(e,H).coeffs()
print(len(eqs))
print(sp.solve(eqs,[R0,k,g1,g2,g4],dict=True))
