# Feasibility of a logarithmic-norm enclosure for the Robertson network (floating point only).
# Reduced system in (y2, y3), y1 = 1 - y2 - y3.
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize_scalar
k1, k2, k3 = 0.04, 1e4, 3e7
def F(t, y):
    y2, y3 = y
    y1 = 1 - y2 - y3
    return [k1*y1 - k2*y2*y3 - k3*y2*y2, k3*y2*y2]
def J(y):
    y2, y3 = y
    return np.array([[-k1 - k2*y3 - 2*k3*y2, -k1 - k2*y2], [2*k3*y2, 0.0]])
def lognorm(A, d):
    D = np.diag([d, 1.0]); B = D @ A @ np.linalg.inv(D); S = (B + B.T)/2
    return np.linalg.eigvalsh(S)[-1]
T = 40.0
sol = solve_ivp(F, (0, T), [0, 0], method='Radau', rtol=1e-12, atol=1e-16, dense_output=True)
print('y(40) =', 1-sol.y[0,-1]-sol.y[1,-1], sol.y[0,-1], sol.y[1,-1])
ts = np.concatenate([np.linspace(0, 1e-3, 200), np.geomspace(1e-3, T, 400)])
for dfix in [None, 30.0, 100.0, 300.0]:
    mus = []
    for t in ts:
        A = J(sol.sol(t))
        if dfix is None:
            r = minimize_scalar(lambda ld: lognorm(A, np.exp(ld)), bounds=(-5, 15), method='bounded')
            mus.append(r.fun)
        else:
            mus.append(lognorm(A, dfix))
    mus = np.array(mus)
    integ = np.trapezoid(mus, ts)
    print('d =', dfix, ' max mu', mus.max(), ' int mu', integ, ' amplification', np.exp(integ))
# Optimal d along trajectory
for t in [0, 1e-5, 1e-4, 1e-3, 1e-2, 0.1, 1, 10, 40]:
    A = J(sol.sol(t))
    r = minimize_scalar(lambda ld: lognorm(A, np.exp(ld)), bounds=(-5, 15), method='bounded')
    print(f't={t:g} y2={sol.sol(t)[0]:.3e} y3={sol.sol(t)[1]:.3e} dopt={np.exp(r.x):.3g} mu={r.fun:.4g}')
