"""Float study (run 2026-11-14T1428Z, unchecked): from the certified state at s = 2000 (BEH2Chain end),
the second minimum of the Bonnor-Ebert mass, the weighted log norm with N(e) = 7 e1^2 + (e1 + 2 e2)^2,
and the Volterra-tail requirement (min of u v^3 on the sublevel set of V through the state at S)."""
import numpy as np, math
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, minimize_scalar
u0, v0 = 0.9804962057, 2.0327898293
f = lambda t, y: [y[0]*(3-y[0]-y[1]), y[1]*(y[0]-1)]
sol = solve_ivp(f, [math.log(2000), math.log(2e5)], [u0, v0], rtol=1e-12, atol=1e-14, dense_output=True)
g = lambda t: 2*sol.sol(t)[0]-sol.sol(t)[1]
# zeros of 2u - v (extrema of m)
ts = np.linspace(math.log(2000), math.log(2e5), 4000); z = []
for a, b in zip(ts[:-1], ts[1:]):
    if g(a)*g(b) < 0: z.append(brentq(g, a, b, xtol=1e-14))
for t in z:
    u, v = sol.sol(t); m = math.sqrt(u*v**3/(4*math.pi))
    print('extremum s=%.4f u=%.10f v=%.10f m=%.8f contrast=%.6g' % (math.exp(t), u, v, m, math.exp(2*t)/(2*u*u)))
N = lambda e: 7*e[0]**2 + (e[0]+2*e[1])**2
def mu(m1, m2):
    J = np.array([[3-2*m1-m2, -m1], [m2, m1-1]])
    M = np.array([[8., 2.], [2., 4.]])  # N(e) = e^T M e
    # max of e^T M J e / e^T M e  = max eig of sym(L J L^-1), M = L^T L
    L = np.linalg.cholesky(M).T; A = L @ J @ np.linalg.inv(L)
    return max(np.linalg.eigvalsh((A+A.T)/2))
worst = -9
for s in np.geomspace(2000, 30000, 300):
    u, v = sol.sol(math.log(s)); worst = max(worst, mu(u, v))
print('max mu_N on [2000, 30000] (per unit log s):', worst)
V = lambda u, v: (u-1-math.log(u)) + (v-2-2*math.log(v/2))
for S in [10000, 12000, 15000, 20000, 25000, 30000]:
    u, v = sol.sol(math.log(S)); lev = V(u, v)
    # min of u v^3 on {V <= lev}: parametrise boundary
    best = 9
    for th in np.linspace(0, 2*math.pi, 2000):
        # ray from (1,2) in direction th, find boundary
        d = (math.cos(th), 2*math.sin(th))
        r = brentq(lambda r: V(1+r*d[0], 2+r*d[1]) - lev, 0, 0.99/ max(1e-9, max(-d[0], -d[1]/2, 1e-9)) if max(-d[0], -d[1]/2) > 0 else 5)
        uu, vv = 1+r*d[0], 2+r*d[1]; best = min(best, uu*vv**3)
    print('S=%6d V=%.3e min uv^3 on sublevel %.6f -> m %.6f' % (S, lev, best, math.sqrt(best/(4*math.pi))))
