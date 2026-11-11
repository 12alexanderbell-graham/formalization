"""Double-precision cross-check (scipy DOP853 + brentq) of beta* and of f''(0) near separation,
with the same parabolic-cylinder tail matching as beta_star_odefun.py.
Usage: nice python3 dop853_check.py
"""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from scipy.special import pbdv


def phi(beta, alpha, eta_inf):
    sol = solve_ivp(lambda t, y: [y[1], y[2], -y[0] * y[2] - beta * (1 - y[1] ** 2)],
                    (0, eta_inf), [0.0, 0.0, alpha], method="DOP853", rtol=1e-13, atol=1e-16)
    f, p, q = sol.y[:, -1]
    nu = -1 - 2 * beta
    r = pbdv(nu + 1, f)[0] / pbdv(nu, f)[0]
    return q - (1 - p) * r


if __name__ == "__main__":
    for e in (7.0, 8.0, 9.0):
        b = brentq(lambda b: phi(b, 0.0, e), -0.19884, -0.19883, xtol=1e-17, rtol=1e-15)
        print(f"eta_inf={e}: beta* = {b:.15f}")
    for beta, br in ((-0.1988, (0.004, 0.006)), (-0.1988, (-0.006, -0.004)),
                     (-0.1, (0.3, 0.33)), (-0.1, (-0.15, -0.13))):
        for e in (8.0, 9.0):
            a = brentq(lambda a: phi(beta, a, e), *br, xtol=1e-16)
            print(f"beta={beta} eta_inf={e}: f''(0) = {a:.12f}")
