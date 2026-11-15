"""Check the planned route's analytic claims on the ball N <= 1/400, N = 7 e1^2 + (e1 + 2 e2)^2,
e1 = u - 1, e2 = v - 2, du/dt = u(3-u-v), dv/dt = v(u-1). Grid in polar coords of (a, b) = (e1, e1 + 2 e2),
N = 7 a^2 + b^2, plus exact identities by sympy."""
import numpy as np
import sympy as sp

e1, e2 = sp.symbols('e1 e2', real=True)
u, v = 1+e1, 2+e2
du, dv = u*(3-u-v), v*(u-1)
N = 7*e1**2 + (e1+2*e2)**2
dN = sp.expand(sp.diff(N, e1)*du + sp.diff(N, e2)*dv)
print("dN/dt + N =", sp.factor(sp.expand(dN + N)))
cross = sp.expand(e1*dv - e2*du)
print("cross =", cross)
uu = sp.symbols('u', positive=True)
g = (2*u - v)
dg = sp.expand(2*du - dv)
print("d(2u-v)/dt at v=2u:", sp.factor(sp.expand(dg.subs(e2, 2*e1).subs(e1, uu-1))))
print("N at v=2u:", sp.factor(sp.expand(N.subs(e2, 2*e1))))
print("u v^3 at v=2u:", sp.factor(sp.expand((u*v**3).subs(e2, 2*e1).subs(e1, uu-1))))
fdN = sp.lambdify((e1, e2), dN, 'numpy')
fcr = sp.lambdify((e1, e2), cross, 'numpy')

th = np.linspace(0, 2*np.pi, 200001)
worst_dN, worst_cr = -np.inf, np.inf
for r in np.linspace(1e-4, 1/20, 500):  # r = sqrt(N)
    a = r*np.cos(th)/np.sqrt(7); b = r*np.sin(th)
    E1 = a; E2 = (b-a)/2
    worst_dN = max(worst_dN, np.max(fdN(E1, E2)/r**2))
    worst_cr = min(worst_cr, np.min(fcr(E1, E2)/(E1**2+E2**2)))
print("sup over ball of (dN/dt)/N            =", worst_dN, "(claim: <= -1/2)")
print("inf over ball of cross/(e1^2+e2^2)     =", worst_cr, "(claim: >= 1/2)")
# cubic constant K: max |dN/dt + N| / N^{3/2} on N = 1
a = np.cos(th)/np.sqrt(7); b = np.sin(th)
c = a*(-7*a**2 - 10*a*b + b**2)
print("K = max |cubic| on N=1 :", np.max(np.abs(c)), " max cubic:", np.max(c),
      " => sup (dN/dt)/N on ball = -1 + K/20 =", -1 + np.max(c)/20)
# quadratic part of cross min eigenvalue
print("lambda_min of [[2,1/2],[1/2,1]] =", (3-np.sqrt(2))/2)
print("lambda_min of [[8,2],[2,4]] =", 6-2*np.sqrt(2))
# ratio derivative (e1/(2e1-e2))' = cross/(2e1-e2)^2 >= cross/(5(e1^2+e2^2))
print("rate of (u-1)/(2u-v) in t >= ", worst_cr/5)
# on the ball: u range
print("max |e1| on ball:", (1/20)*np.sqrt(4/28), " (|a| <= sqrt(N/(7- ...)))")
E1 = (1/20)*np.cos(th)/np.sqrt(7)
print("grid max |e1| on N=1/400:", np.max(np.abs(E1)), " max |e2|:", np.max(np.abs(((1/20)*np.sin(th)-E1)/2)))
