"""(1) Which truncation L reproduces each printed f''(0) at beta = -0.1988 (BC f'(L)=1, or f''(L)=0)?
(2) Cross-check of the collocation value by smooth-residual shooting (DOP853, rtol 1e-13) with the
    Gaussian-tail Robin matching residual  q - (1-p) D_{nu+1}(f)/D_nu(f)  at eta_inf, Brent root in alpha
    (not overshoot classification).
(3) Profile checks: min f'' on [0, eta_inf], q/(1-p) growth (decay class), normalisation conversions.

Usage: nice python3 truncation_and_crosscheck.py
"""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from scipy.special import pbdv

import importlib.util, os
spec = importlib.util.spec_from_file_location(
    "bvp", os.path.join(os.path.dirname(os.path.abspath(__file__)), "bvp_collocation.py"))
bvp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bvp)

BETA, NU = bvp.BETA, bvp.NU


def shoot(alpha, L, dense=False):
    def F(t, y):
        return [y[1], y[2], -y[0] * y[2] - BETA * (1 - y[1] ** 2)]
    return solve_ivp(F, [0, L], [0.0, 0.0, alpha], method="DOP853", rtol=1e-13, atol=1e-16,
                     dense_output=dense)


def resid(alpha, L):
    s = shoot(alpha, L)
    f, p, q = s.y[:, -1]
    return q - (1 - p) * pbdv(NU + 1, f)[0] / pbdv(NU, f)[0]


if __name__ == "__main__":
    print("== (2) smooth-residual shooting with tail matching ==", flush=True)
    for L in [7, 8, 9, 10]:
        a = brentq(resid, 0.0050, 0.0054, args=(L,), xtol=1e-16, rtol=1e-15)
        print(f"L={L} alpha={a:.13f}", flush=True)
    a_true = 0.0052181878839

    print("== (3) profile checks at the collocation solution, L=10 ==", flush=True)
    s = bvp.solve(10.0, bvp.bc_robin, tol=1e-11)
    eta, (f, p, q) = s.x, s.y
    print(f"min q on [0,10] = {q.min():.3e} at eta={eta[q.argmin()]:.3f}; q>0 everywhere: {bool((q > 0).all())}")
    print(f"max p = {p.max():.15f} (<1: {bool(p.max() < 1)})")
    for e in [3, 4, 5, 6, 7, 8, 9]:
        i = np.searchsorted(eta, e)
        print(f"eta={eta[i]:.2f}  q/(1-p)={q[i] / (1 - p[i]):.4f}  eta-delta={eta[i] - 2.33298:.4f}")
    m = BETA / (2 - BETA)
    c = (m + 1) / 2
    print(f"m = beta/(2-beta) = {m:.12f}; F''(0) in f'''+((m+1)/2)ff''+m(1-f'^2)=0: {np.sqrt(c) * a_true:.12f}")
    print(f"f''(0)*sqrt(2) (Blasius-type x2 scaling): {np.sqrt(2) * a_true:.12f}")
    K = 2500 / 497
    print(f"K={K:.12f}  A = sqrt(K) f''(0) = {np.sqrt(K) * a_true:.13f}; "
          f"window in A: ({np.sqrt(K) * 0.0052181:.12f}, {np.sqrt(K) * 0.0052182:.12f})")

    print("== (1) truncation length reproducing each printed value ==", flush=True)

    def a_of(L, bc):
        return bvp.solve(L, bc, tol=1e-10).y[2, 0]
    for val in [0.005221, 0.005222, 0.005225, 0.005226, 0.005229]:
        for name, bc in [("f'(L)=1", bvp.bc_dirichlet), ("f''(L)=0", bvp.bc_neumann)]:
            try:
                L = brentq(lambda L: a_of(L, bc) - val, 7.0, 10.0, xtol=1e-4)
                print(f"printed {val}: {name} at L = {L:.3f}", flush=True)
            except Exception as ex:
                print(f"printed {val}: {name}: {ex}", flush=True)
    for L in [6.68, 7.51]:
        print(f"L={L}: f'(L)=1 -> {a_of(L, bvp.bc_dirichlet):.7f}; f''(L)=0 -> {a_of(L, bvp.bc_neumann):.7f}",
              flush=True)
