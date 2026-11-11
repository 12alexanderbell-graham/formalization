"""Referee (run 2026-11-11T1228Z), Method A: collocation for the REVERSED-flow Falkner-Skan branch.

f''' + f f'' + beta (1 - f'^2) = 0, f(0) = f'(0) = 0, beta = -0.1988.
scipy.integrate.solve_bvp (Lobatto IIIA, adaptive mesh) on [0, L] with the parabolic-cylinder (Robin) tail
    f''(L) = (1 - f'(L)) D_{nu+1}(x)/D_nu(x),   x = f(L),   nu = -1 - 2 beta,
which keeps only the Gaussian mode g = 1 - f' = e^{-x^2/4} D_nu(x) of g'' + x g' - 2 beta g = 0.
The initial guess is a hand-made profile with a reversed-flow dip (no shooting is used).
Also reports the class conditions of the converged profile (|f'| <= 1, f''/(1 - f') growth).

Usage: nice python3 rev_collocation.py
"""
import numpy as np
from scipy.integrate import solve_bvp
from scipy.special import pbdv

BETA = -0.1988
NU = -1 - 2 * BETA


def rhs(eta, y):
    f, p, q = y
    return np.vstack([p, q, -f * q - BETA * (1 - p * p)])


def bc_robin(ya, yb):
    x = yb[0]
    r = pbdv(NU + 1, x)[0] / pbdv(NU, x)[0]
    return np.array([ya[0], ya[1], yb[2] - (1 - yb[1]) * r])


def bc_dirichlet(ya, yb):
    return np.array([ya[0], ya[1], yb[1] - 1.0])


def bc_neumann(ya, yb):
    return np.array([ya[0], ya[1], yb[2]])


def guess(L, n0=600, dip=0.0, d=3.5):
    """Smooth profile: tanh-like rise to 1 near eta ~ d, with an optional reversed-flow dip near the wall."""
    eta = np.linspace(0, L, n0)
    p = 1 - np.exp(-((eta / d) ** 4)) * (1 + 0 * eta)  # p ~ (eta/d)^4 near the wall: flat at the wall
    p = p - dip * (eta / 1.5) ** 2 * np.exp(-((eta / 1.5) ** 2))
    f = np.concatenate([[0], np.cumsum((p[1:] + p[:-1]) / 2 * np.diff(eta))])
    q = np.gradient(p, eta)
    return eta, np.vstack([f, p, q])


def solve(L, bc, tol=1e-11, dip=0.0, d=3.5, prev=None, n0=2000):
    if prev is None:
        eta, y = guess(L, dip=dip, d=d)
    else:
        eta = np.linspace(0, L, n0)
        y = prev.sol(np.minimum(eta, prev.x[-1]))
    return solve_bvp(rhs, bc, eta, y, tol=tol, max_nodes=3_000_000, bc_tol=1e-15)


if __name__ == "__main__":
    print("== guesses: which branch does Newton land on ==", flush=True)
    for dip in [0.0, 0.01, 0.03, 0.06]:
        for d in [3.0, 3.5, 4.0]:
            s = solve(10, bc_robin, tol=1e-8, dip=dip, d=d)
            print(f"dip={dip:5.2f} d={d:3.1f} status={s.status} f''(0)={s.y[2, 0]:+.10f} min f'={s.y[1].min():+.6f}",
                  flush=True)
    print("== Robin tail, reversed branch ==", flush=True)
    base = solve(10, bc_robin, tol=1e-8, dip=0.03, d=3.5)
    assert base.y[2, 0] < 0, "did not land on the reversed branch"
    res = {}
    for L in [8, 9, 10, 11, 12, 13, 14, 16]:
        for tol in [1e-10, 1e-11]:  # tol 1e-12 does not terminate in scipy 1.18 here
            s = solve(L, bc_robin, tol=tol, prev=base)
            res[(L, tol)] = s
            print(f"L={L:4.1f} tol={tol:.0e} status={s.status} nodes={s.x.size:7d} f''(0)={s.y[2, 0]:+.14f} "
                  f"max resid={np.max(s.rms_residuals):.1e} delta={L - s.y[0, -1]:.10f}", flush=True)
        s2 = solve(L, bc_robin, tol=1e-11, prev=base, n0=40000)
        print(f"L={L:4.1f} tol=1e-11 initial mesh 40000: status={s2.status} nodes={s2.x.size} "
              f"f''(0)={s2.y[2, 0]:+.14f}", flush=True)
    s = res[(12, 1e-11)]
    eta = s.x
    f, p, q = s.y
    print("== class conditions on the L=12 tol=1e-11 profile ==")
    i = np.argmin(p)
    print(f"min f' = {p[i]:+.10f} at eta = {eta[i]:.6f};  max f' = {p.max():.15f};  max f' < 1: {bool((p < 1).all())}")
    zq = eta[np.where(np.diff(np.sign(q)) != 0)[0]]
    print("sign changes of f'' at eta ~", np.round(zq, 6))
    zp = eta[np.where(np.diff(np.sign(p[1:])) != 0)[0] + 1]
    print("zero of f' (end of reversed-flow region) at eta ~", np.round(zp, 6))
    for e in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]:
        pp, qq = s.sol(e)[1], s.sol(e)[2]
        print(f"eta={e:4.1f} f'={pp:+.12f} f''={qq:+.6e} f''/(1-f')={qq / (1 - pp):9.4f} x=eta-delta={e - (12 - f[-1]):.4f}")
