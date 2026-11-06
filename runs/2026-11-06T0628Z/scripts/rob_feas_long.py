# Feasibility of the one-sided (log-norm) enclosure for Robertson at long horizons, t in [40, 1e11]
# (floating point only; informs the next certified step). Reduced system in (y2, y3), y1 = 1 - y2 - y3.
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize_scalar
k1, k2, k3 = 0.04, 1e4, 3e7
def F(t, y):
    y2, y3 = y; y1 = 1 - y2 - y3
    return [k1*y1 - k2*y2*y3 - k3*y2*y2, k3*y2*y2]
def J(y):
    y2, y3 = y
    return np.array([[-k1 - k2*y3 - 2*k3*y2, -k1 - k2*y2], [2*k3*y2, 0.0]])
def lognorm(A, d):
    D = np.diag([d, 1.0]); B = D @ A @ np.linalg.inv(D); S = (B + B.T)/2
    return np.linalg.eigvalsh(S)[-1]
sol = solve_ivp(F, (0, 1e11), [0, 0], method='Radau', rtol=1e-12, atol=1e-20, dense_output=True)
for T in [40, 4e2, 4e3, 4e4, 4e5, 4e6, 4e7, 4e8, 4e9, 4e10, 1e11]:
    y = sol.sol(T); print(f'T={T:g} y1={1-y[0]-y[1]:.10e} y2={y[0]:.10e} y3={y[1]:.10e}')
# cells geometric from 40, ratio q; one weight per cell (optimal at the cell midpoint); mu = max over cell samples
for q in [1.2, 1.5, 2.0]:
    edges = [40.0]
    while edges[-1] < 1e11: edges.append(min(edges[-1]*q, 1e11))
    tot, worst, inc = 0.0, -1e9, 0.0
    dprev = None
    for a, b in zip(edges[:-1], edges[1:]):
        A = J(sol.sol(np.sqrt(a*b)))
        r = minimize_scalar(lambda ld: lognorm(A, np.exp(ld)), bounds=(-10, 15), method='bounded')
        d = np.exp(r.x)
        mu = max(lognorm(J(sol.sol(t)), d) for t in np.geomspace(a, b, 12))
        tot += mu*(b-a); worst = max(worst, mu)
        if dprev is not None and d > dprev: inc += np.log(d/dprev)
        dprev = d
    print(f'q={q}: cells {len(edges)-1}, int mu dt = {tot:.3g} (amplification {np.exp(min(tot,700)):.3g}), max mu {worst:.3g}, log weight increases {inc:.3g}, final d {dprev:.3g}')
