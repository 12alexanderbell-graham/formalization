#!/usr/bin/env python3
"""Referee computation B: global collocation (scipy.integrate.solve_bvp, 4th-order Lobatto IIIa)
on [0, L] with the asymptotic Robin condition at L
    f''(L) = R(f(L)) (1 - f'(L)),  R(xi) = D_{nu+1}(xi)/D_nu(xi),  nu = -1 - 2 beta
(parabolic-cylinder ratio for the fast-decaying mode of g'' + xi g' - 2 beta g = 0, g = 1 - f').
Then Richardson-free convergence check in L and tolerance.
"""
import numpy as np
from scipy.integrate import solve_bvp
from scipy.special import pbdv

rows = [(-0.15, 0.2163614), (-0.18, 0.1286362), (-0.19, 0.0857), (-0.195, 0.05517), (-0.198, 0.02509)]


def R(beta, xi):
    nu = -1 - 2 * beta
    return pbdv(nu + 1, xi)[0] / pbdv(nu, xi)[0]


def solve(beta, L, s0, tol=1e-12, n=4000):
    def fun(x, y):
        f, p, q = y
        return np.vstack([p, q, -f * q - beta * (1 - p ** 2)])

    def bc(ya, yb):
        return np.array([ya[0], ya[1], yb[2] - R(beta, yb[0]) * (1 - yb[1])])

    x = np.linspace(0, L, n)
    # initial guess: f' = 1 - exp(-x^2 / ...) shape with given wall shear
    p = 1 - np.exp(-0.15 * x ** 2)
    f = np.concatenate([[0], np.cumsum((p[1:] + p[:-1]) / 2 * np.diff(x))])
    q = np.gradient(p, x)
    sol = solve_bvp(fun, bc, x, np.vstack([f, p, q]), tol=tol, max_nodes=400000, bc_tol=1e-14)
    return sol


if __name__ == '__main__':
    for beta, s0 in rows:
        for L in (8, 10, 12, 14):
            sol = solve(beta, L, s0)
            print(f"beta={beta:7} L={L:3d} status={sol.status} nodes={sol.x.size:6d} "
                  f"maxres={np.max(sol.rms_residuals):.1e} s={sol.y[2, 0]:.15f}", flush=True)
