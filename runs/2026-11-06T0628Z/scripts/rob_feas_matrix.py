# Long-horizon Robertson: log norm with a diagonal weight vs a full 2x2 weight (L^T L, L lower triangular).
# Diagonal weights give mu >= 0 (no contraction: the t = 40 radius would persist); a full weight should
# see the slaved slow mode's decay (perturbations of y1 ~ 1/t decay like t^-2, rate -2/t).
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize
k1, k2, k3 = 0.04, 1e4, 3e7
def F(t, y):
    y2, y3 = y; y1 = 1 - y2 - y3
    return [k1*y1 - k2*y2*y3 - k3*y2*y2, k3*y2*y2]
def J(y):
    y2, y3 = y
    return np.array([[-k1 - k2*y3 - 2*k3*y2, -k1 - k2*y2], [2*k3*y2, 0.0]])
def ln(A, L):
    B = L @ A @ np.linalg.inv(L); return np.linalg.eigvalsh((B + B.T)/2)[-1]
sol = solve_ivp(F, (0, 1e11), [0, 0], method='Radau', rtol=1e-10, atol=1e-20, dense_output=True)
for t in [40, 400, 4e3, 4e4, 4e5, 4e6, 4e8, 4e10]:
    A = J(sol.sol(t)); ev = np.linalg.eigvals(A)
    best = None
    for x0 in [(np.log(10), 0.0), (np.log(0.01), 0.0), (np.log(1.0), 1.0)]:
        r = minimize(lambda p: ln(A, np.array([[np.exp(p[0]), 0], [p[1], 1.0]])), x0, method='Nelder-Mead',
                     options=dict(xatol=1e-12, fatol=1e-16, maxiter=4000))
        if best is None or r.fun < best.fun: best = r
    dd = min(ln(A, np.diag([np.exp(l), 1.0])) for l in np.linspace(-12, 8, 2001))
    print(f't={t:g} eig={np.sort(ev.real)} diag-best mu={dd:.3e} full-best mu={best.fun:.3e} -2/t={-2/t:.3e} L={best.x}')
