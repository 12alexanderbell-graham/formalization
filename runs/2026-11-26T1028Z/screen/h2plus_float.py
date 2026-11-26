"""Floating-point scratch check of the H2+ candidate (run 2026-11-26T1028Z, section Screen): NOT evidence.
Separated equations (atomic units, nuclei of charge 1 at distance R, m = 0, k = -E R^2 / 2 > 0, E electronic):
  eta: -[(1 - eta^2) M']' - k eta^2 M = A M          (M regular at eta = +-1, even for sigma_g)
  xi : [(xi^2 - 1) L']' + (2 R xi - k xi^2 - A) L = 0 (L regular at xi = 1, decaying as xi -> infinity)
A(E) is the lowest even eigenvalue of the eta problem (Legendre basis); E is found by shooting L from xi = 1."""
import numpy as np
from scipy.integrate import solve_ivp
from numpy.polynomial.legendre import leggauss
from scipy.special import eval_legendre

R = 2.0
NB = 30
x, wq = leggauss(200)

def A_of(k):
    ns = np.arange(0, 2 * NB, 2)
    P = np.array([eval_legendre(n, x) * np.sqrt((2 * n + 1) / 2) for n in ns])
    H = np.diag(ns * (ns + 1.0)) - k * (P * wq * x ** 2) @ P.T
    return np.linalg.eigvalsh(H)[0]

def tail_sign(E, xmax=12.0):
    k = -E * R ** 2 / 2
    A = A_of(k)
    c = 2 * R - k - A
    h = 1e-6
    L1 = 1.0 - c / 2 * h
    dL1 = -c / 2
    def f(xi, y):
        L, dL = y
        return [dL, (-2 * xi * dL - (2 * R * xi - k * xi ** 2 - A) * L) / (xi ** 2 - 1)]
    sol = solve_ivp(f, [1 + h, xmax], [L1, dL1], rtol=1e-12, atol=1e-14)
    return np.sign(sol.y[0, -1]), A

lo, hi = -1.2, -1.0
slo, _ = tail_sign(lo)
for _ in range(60):
    mid = (lo + hi) / 2
    s, A = tail_sign(mid)
    if s == slo:
        lo = mid
    else:
        hi = mid
print(f"R = {R}: electronic E = {mid:.12f}, total E + 1/R = {mid + 1 / R:.12f}, separation constant A = {A:.10f}")
