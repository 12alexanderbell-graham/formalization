"""Referee (run 2026-11-11T1228Z): sanity check of the reversed-branch collocation (Robin parabolic-cylinder tail)
at other beta against printed reversed-flow values (Fazio 2012 Table 4; Belden-...-Barlow 2019 Fig. 2 caption).
Usage: nice python3 cross_beta.py"""
import numpy as np
from scipy.integrate import solve_bvp
from scipy.special import pbdv

def solve(beta, L, tol=1e-10):
    nu = -1 - 2 * beta
    rhs = lambda t, y: np.vstack([y[1], y[2], -y[0] * y[2] - beta * (1 - y[1] ** 2)])
    def bc(ya, yb):
        return np.array([ya[0], ya[1], yb[2] - (1 - yb[1]) * pbdv(nu + 1, yb[0])[0] / pbdv(nu, yb[0])[0]])
    eta = np.linspace(0, L, 3000)
    a = 2.0 if beta > -0.05 else 1.5  # depth/width of the hand-made reversed dip
    p = 1 - np.exp(-(eta / 4.0) ** 2) - 0.3 * (eta / a) * np.exp(-(eta / a) ** 2) * (1 + 0 * eta)
    p = np.clip(p, -0.5, 1)
    f = np.concatenate([[0], np.cumsum((p[1:] + p[:-1]) / 2 * np.diff(eta))])
    q = np.gradient(p, eta)
    return solve_bvp(rhs, bc, eta, np.vstack([f, p, q]), tol=tol, max_nodes=2_000_000)

printed = [(-0.025, -0.074366, "Fazio ITM"), (-0.05, -0.108271, "Fazio ITM"), (-0.1, -0.140546, "Fazio/Asaithambi/Auteri"),
           (-0.15, -0.133421, "Fazio/Asaithambi/Auteri"), (-0.18, -0.097692, "Fazio/Asaithambi/Auteri"),
           (-0.12, -0.1429351943576, "Barlow V"), (-0.02, -0.065168585542904, "Barlow VI")]
for beta, val, src in printed:
    out = []
    for L in ([30, 40] if beta > -0.06 else [14, 18]):
        s = solve(beta, L)
        out.append((L, s.status, s.y[2, 0]))
    print(f"beta={beta:+.4f} printed {val:+.13f} ({src}); computed " +
          "; ".join(f"L={L} st={st} {v:+.13f}" for L, st, v in out), flush=True)

# Ganapol 2010 (arXiv:1006.3888) Table 7/8 reversed-flow values close to separation, and this run's beta
print("== near separation: continuation from beta = -0.18 ==", flush=True)
from scipy.integrate import solve_bvp as _sb
s = solve(-0.18, 14)
for beta, val in [(-0.19, -7.13359060034e-02), (-0.196348, -4.00005870180e-02), (-0.198826, -2.88367895808e-03),
                  (-0.1988, None), (-0.198837735, -5.77014e-06)]:
    nu = -1 - 2 * beta
    rhs = lambda t, y, b=beta: np.vstack([y[1], y[2], -y[0] * y[2] - b * (1 - y[1] ** 2)])
    bc = lambda ya, yb, n=nu: np.array([ya[0], ya[1], yb[2] - (1 - yb[1]) * pbdv(n + 1, yb[0])[0] / pbdv(n, yb[0])[0]])
    s = _sb(rhs, bc, s.x, s.y, tol=1e-11, max_nodes=2_000_000)
    print(f"beta={beta:+.9f} printed {val} computed {s.y[2, 0]:+.12e} status {s.status}", flush=True)
