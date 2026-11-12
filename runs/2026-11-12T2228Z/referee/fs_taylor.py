#!/usr/bin/env python3
"""Referee's independent Falkner-Skan solver (arbitrary precision Taylor-series integrator, mpmath).

f''' + f f'' + beta (1 - f'^2) = 0,  f(0)=0, f'(0)=0, f'(inf)=1.
Shooting parameter s = f''(0).  Far-field condition: p(L) = f'(L) = 1 at finite L
(for beta<0 the error is exponentially small in L^2: the condition kills the algebraic mode
g ~ eta^(2 beta) of g = 1 - p up to the size of the Gaussian mode at L).
"""
import sys
import mpmath as mp


def taylor_step(f0, p0, q0, beta, h, N):
    """One Taylor step of order N. Returns (f,p,q) at t0+h."""
    a = [f0, p0, q0 / 2]
    # b_k = (k+1) a_{k+1}  (coeffs of f'),  c_k = (k+1)(k+2) a_{k+2} (coeffs of f'')
    for k in range(0, N - 2):
        # coeff k of f*f''
        s1 = mp.fsum(a[i] * (k - i + 1) * (k - i + 2) * a[k - i + 2] for i in range(k + 1))
        s2 = mp.fsum((i + 1) * a[i + 1] * (k - i + 1) * a[k - i + 1] for i in range(k + 1))
        rhs = -s1 + beta * s2
        if k == 0:
            rhs -= beta
        a.append(rhs / ((k + 1) * (k + 2) * (k + 3)))
    # evaluate by Horner
    f = mp.mpf(0); p = mp.mpf(0); q = mp.mpf(0)
    for k in range(N, -1, -1):
        f = f * h + a[k]
    for k in range(N, 0, -1):
        p = p * h + k * a[k]
    for k in range(N, 1, -1):
        q = q * h + k * (k - 1) * a[k]
    return f, p, q


def integrate(beta, s, L, h, N, record=False, blow=50):
    f = mp.mpf(0); p = mp.mpf(0); q = mp.mpf(s)
    n = int(mp.nint(L / h))
    pmin = p; pmax = p
    traj = []
    for i in range(n):
        f, p, q = taylor_step(f, p, q, beta, h, N)
        if p < pmin: pmin = p
        if p > pmax: pmax = p
        if record:
            traj.append(((i + 1) * h, f, p, q))
        if abs(p) > blow:
            return None, (pmin, pmax, traj)
    return (f, p, q), (pmin, pmax, traj)


def F(beta, s, L, h, N):
    r, _ = integrate(beta, s, L, h, N)
    if r is None:
        return None
    return r[1] - 1


def solve(beta, s0, s1, L, h, N, tol=None):
    """Secant on F(s) = p(L;s) - 1."""
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 8))
    F0 = F(beta, s0, L, h, N); F1 = F(beta, s1, L, h, N)
    for it in range(60):
        s2 = s1 - F1 * (s1 - s0) / (F1 - F0)
        s0, F0 = s1, F1
        s1 = s2
        F1 = F(beta, s1, L, h, N)
        if abs(s1 - s0) < tol:
            return s1
    raise RuntimeError("no convergence")
