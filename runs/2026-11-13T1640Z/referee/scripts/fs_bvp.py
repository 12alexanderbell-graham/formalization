import numpy as np
from scipy.integrate import solve_bvp
from scipy.special import pbdv

def run(beta, L, robin=True, n=4000):
    nu = -1 - 2 * beta
    def ode(x, y):
        return np.vstack([y[1], y[2], -y[0] * y[2] - beta * (1 - y[1] ** 2)])
    def bc(ya, yb):
        if robin:
            R = pbdv(nu + 1, yb[0])[0] / pbdv(nu, yb[0])[0]
            return np.array([ya[0], ya[1], yb[2] - R * (1 - yb[1])])
        return np.array([ya[0], ya[1], yb[1] - 1])
    x = np.linspace(0, L, n)
    y0 = np.vstack([x - 1 + np.exp(-x), 1 - np.exp(-x), np.exp(-x) * 0.3])
    sol = solve_bvp(ode, bc, x, y0, tol=1e-11, max_nodes=500000)
    return sol.status, sol.sol(0)[2]

for beta in (-0.13, -0.14, -0.16):
    for L in (8, 10, 12, 14):
        st, s = run(beta, L)
        print(beta, 'robin', L, st, repr(s))
    for L in (10, 15, 20, 25):
        st, s = run(beta, L, robin=False)
        print(beta, "f'(L)=1", L, st, repr(s))
