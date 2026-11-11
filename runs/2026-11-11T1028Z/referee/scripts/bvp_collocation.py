"""Independent value of f''(0) for f''' + f f'' + beta(1 - f'^2) = 0, f(0)=f'(0)=0, f'->1, beta=-0.1988.

Method A (collocation): scipy.integrate.solve_bvp (4th-order Lobatto IIIA collocation, adaptive mesh)
on [0, L] with the asymptotic (Robin) tail condition at L:
    f''(L) = (1 - f'(L)) * D_{nu+1}(x)/D_nu(x),  x = f(L) (= L - delta),  nu = -1 - 2 beta,
which selects the Gaussian-decaying mode g = 1 - f' = exp(-x^2/4) D_nu(x) of the linearised tail
g'' + x g' - 2 beta g = 0 (the other mode ~ x^{2 beta} is the algebraic tail).
Also: plain truncations f'(L) = 1 and f''(L) = 0 (what most tables use) to see which L reproduces
the printed values.

Usage: nice python3 bvp_collocation.py
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


def solve(L, bc, tol=1e-11, n0=400, alpha0=0.0052):
    eta = np.linspace(0, L, n0)
    # initial guess: an attached-looking profile with positive shear
    d = 2.36
    p = np.clip(1 - np.exp(-((eta / d) ** 2) * 1.0), 0, 1)
    f = np.concatenate([[0], np.cumsum((p[1:] + p[:-1]) / 2 * np.diff(eta))])
    q = np.gradient(p, eta)
    q[0] = alpha0
    sol = solve_bvp(rhs, bc, eta, np.vstack([f, p, q]), tol=tol, max_nodes=2_000_000, bc_tol=1e-14)
    return sol


if __name__ == "__main__":
    print("== Robin (asymptotic tail) condition ==", flush=True)
    for L in [8, 9, 10, 11, 12, 14]:
        for tol in [1e-9, 1e-11, 1e-12]:
            s = solve(L, bc_robin, tol=tol)
            print(f"L={L:5.1f} tol={tol:.0e} status={s.status} nodes={s.x.size:7d} "
                  f"f''(0)={s.y[2, 0]:.13f} min f''={s.y[2].min():.3e} delta={L - s.y[0, -1]:.10f}",
                  flush=True)
    print("== plain truncation f'(L)=1 ==", flush=True)
    for L in [4, 4.5, 5, 5.5, 6, 6.5, 7, 7.5, 8, 9, 10, 12]:
        s = solve(L, bc_dirichlet, tol=1e-10)
        print(f"L={L:5.1f} status={s.status} f''(0)={s.y[2, 0]:.10f}", flush=True)
    print("== plain truncation f''(L)=0 ==", flush=True)
    for L in [4, 4.5, 5, 5.5, 6, 6.5, 7, 7.5, 8, 9, 10, 12]:
        s = solve(L, bc_neumann, tol=1e-10)
        print(f"L={L:5.1f} status={s.status} f''(0)={s.y[2, 0]:.10f}", flush=True)
