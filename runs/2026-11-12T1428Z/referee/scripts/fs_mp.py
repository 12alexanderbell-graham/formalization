#!/usr/bin/env python3
"""Referee computation A: high-precision Taylor-series integration (mpmath) of
f''' + f f'' + beta (1 - f'^2) = 0, f(0)=f'(0)=0, f''(0)=s,
with the ASYMPTOTIC far-field condition at eta = L (not f'(L)=1):

  linearised tail g = 1 - f' solves g'' + xi g' - 2 beta g = 0, xi = f(L) (= eta - delta + exp. small);
  the fast-decaying solution is U = exp(-xi^2/4) D_nu(xi), nu = -1 - 2 beta, so
  -g'/g = D_{nu+1}(xi)/D_nu(xi) =: R(xi)   and we impose   f''(L) = R(f(L)) * (1 - f'(L)).

The slowly decaying algebraic mode g ~ xi^{2 beta} (which decays too, since beta < 0) is
exactly what this condition excludes.  Root in s by secant (mp.findroot).
Usage: python3 fs_mp.py [dps] [order] [h]
"""
import sys
from mpmath import mp, mpf, pcfd, findroot, nstr

dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
ORDER = int(sys.argv[2]) if len(sys.argv) > 2 else 40
H = mpf(sys.argv[3]) if len(sys.argv) > 3 else mpf('0.125')
mp.dps = dps


def taylor_step(f0, p0, q0, beta, h, N):
    a = [mp.zero] * (N + 3)
    a[0], a[1], a[2] = f0, p0, q0 / 2
    for k in range(N):
        s1 = mp.fsum(a[i] * (k - i + 1) * (k - i + 2) * a[k - i + 2] for i in range(k + 1))
        s2 = mp.fsum((i + 1) * a[i + 1] * (k - i + 1) * a[k - i + 1] for i in range(k + 1))
        rhs = -s1 + beta * s2 - (beta if k == 0 else 0)
        a[k + 3] = rhs / ((k + 1) * (k + 2) * (k + 3))
    # evaluate f, f', f'' at h (Horner)
    f = p = q = mp.zero
    for k in range(N + 2, -1, -1):
        f = f * h + a[k]
    for k in range(N + 2, 0, -1):
        p = p * h + k * a[k]
    for k in range(N + 2, 1, -1):
        q = q * h + k * (k - 1) * a[k]
    return f, p, q


def integrate(s, beta, L, h=H, N=ORDER):
    f, p, q = mp.zero, mp.zero, mpf(s)
    n = int(mp.nint(L / h))
    for _ in range(n):
        f, p, q = taylor_step(f, p, q, beta, h, N)
    return f, p, q


def resid(s, beta, L):
    f, p, q = integrate(s, beta, L)
    nu = -1 - 2 * beta
    R = pcfd(nu + 1, f) / pcfd(nu, f)
    return q - R * (1 - p)


def resid_plain(s, beta, L):
    f, p, q = integrate(s, beta, L)
    return p - 1


def solve(beta, L, s0, cond=resid):
    return findroot(lambda s: cond(s, beta, L), (mpf(s0), mpf(s0) * (1 + mpf('1e-6'))),
                    solver='secant', tol=mpf(10) ** (-2 * mp.dps + 10), maxsteps=60)


if __name__ == '__main__':
    rows = [('-0.15', '0.2163614'), ('-0.18', '0.1286362'), ('-0.19', '0.0857'),
            ('-0.195', '0.05517'), ('-0.198', '0.02509')]
    Ls = [int(x) for x in (sys.argv[4].split(',') if len(sys.argv) > 4 else ['6', '8', '10', '12'])]
    print(f"dps={mp.dps} order={ORDER} h={H}")
    for b, s0 in rows:
        beta = mpf(b)
        for L in Ls:
            s = solve(beta, L, s0)
            print(f"beta={b:7s} L={L:3d} asym  s={nstr(s, 25)}", flush=True)
        for L in Ls[-2:]:
            s = solve(beta, L, s0, resid_plain)
            print(f"beta={b:7s} L={L:3d} plain s={nstr(s, 25)}", flush=True)
