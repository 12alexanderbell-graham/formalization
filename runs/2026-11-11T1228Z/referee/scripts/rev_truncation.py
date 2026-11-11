"""Referee (run 2026-11-11T1228Z): truncation study for the reversed branch + double-precision cross-check.

(T) naive truncations on [0, L]: f'(L) = 1 (Dirichlet) and f''(L) = 0 (Neumann), reversed root followed by
    secant from the tail-matched value; which L reproduces Fazio's printed -0.005158?
(D) scipy DOP853 (rtol 1e-13) integration of the IVP with f''(0) = -0.005158: first eta with f' = 1, peak.
(E) precise first crossing f' = 1 for the printed value in multiprecision (bisection on the Taylor step).

Usage: nice python3 rev_truncation.py
"""
import mpmath as mp
import numpy as np
from scipy.integrate import solve_ivp

import rev_taylor as rt

mp.mp.dps = 30
ALPHA_TRUE = mp.mpf("-0.00515742017792910414908")


def endpoint(alpha, L):
    """(f, f', f'') at L with the Taylor integrator: steps of 1/16 then one partial step."""
    n = int(mp.floor(L * 16))
    y = rt.integrate(alpha, mp.mpf(n) / 16)
    rem = mp.mpf(L) - mp.mpf(n) / 16
    if rem > 0:
        y = rt.taylor_step(*y, h=rem)
    return y


def secant(fun, a0, a1, tol=mp.mpf(10) ** -22):
    r0, r1 = fun(a0), fun(a1)
    for _ in range(60):
        if r1 == r0:
            break
        a2 = a1 - r1 * (a1 - a0) / (r1 - r0)
        a0, r0, a1 = a1, r1, a2
        r1 = fun(a1)
        if abs(a1 - a0) < tol:
            break
    return a1


def naive_root(L, kind, seed=ALPHA_TRUE):
    if kind == "dirichlet":
        fun = lambda a: endpoint(a, L)[1] - 1
    else:
        fun = lambda a: endpoint(a, L)[2]
    return secant(fun, seed, seed * (1 + mp.mpf("1e-6")))


if __name__ == "__main__":
    print("== (T) naive truncation, reversed branch (continuation from L = 12 downwards) ==", flush=True)
    for kind in ["dirichlet", "neumann"]:
        table = []
        seed = ALPHA_TRUE
        for L in [mp.mpf(x) / 4 for x in range(48, 25, -1)]:
            a = naive_root(L, kind, seed)
            seed = a
            table.append((L, a))
            print(f"{kind:9s} L={mp.nstr(L, 5):>6} f''(0)={mp.nstr(a, 12)}", flush=True)
        for target in ["-0.0051575", "-0.005158", "-0.0051585"]:
            tv = mp.mpf(target)
            for (L0, a0), (L1, a1) in zip(table, table[1:]):
                if (a0 - tv) * (a1 - tv) <= 0:
                    g = lambda L: naive_root(L, kind, a0) - tv
                    Ls = mp.findroot(g, (L1, L0), solver="secant", tol=mp.mpf(10) ** -24)
                    print(f"  {kind}: f''(0) = {target} at L = {mp.nstr(Ls, 8)}", flush=True)
                    break
            else:
                print(f"  {kind}: {target} not reached for L in [6.5, 12]")

    print("== (D) DOP853 cross-check of the printed IVP ==", flush=True)
    beta = -0.1988

    def rhs(t, y):
        return [y[1], y[2], -y[0] * y[2] - beta * (1 - y[1] ** 2)]

    ev = lambda t, y: y[1] - 1.0
    ev.direction = 1
    for alpha in [-0.005158, float(ALPHA_TRUE)]:
        s = solve_ivp(rhs, (0, 60), [0, 0, alpha], method="DOP853", rtol=1e-13, atol=1e-16, events=ev,
                      dense_output=True)
        ts = np.linspace(0, 60, 600001)
        p = s.sol(ts)[1]
        i = np.argmax(p)
        print(f"alpha={alpha:+.14f}: first up-crossing f'=1 at eta = {s.t_events[0][:1]}, max f' - 1 = {p[i] - 1:.4e} "
              f"at eta = {ts[i]:.4f}, f'(60) - 1 = {p[-1] - 1:.3e}", flush=True)

    print("== (E) multiprecision first crossing for alpha = -0.005158 ==", flush=True)
    a = mp.mpf("-0.005158")
    lo, hi = mp.mpf(8), mp.mpf("8.125")
    for _ in range(50):
        mid = (lo + hi) / 2
        if endpoint(a, mid)[1] > 1:
            hi = mid
        else:
            lo = mid
    print(f"f' = 1 first at eta = {mp.nstr(lo, 12)} (f'(8) - 1 = {mp.nstr(endpoint(a, 8)[1] - 1, 6)})")
    best = max(((mp.mpf(k) / 64, endpoint(a, mp.mpf(k) / 64)[1]) for k in range(8 * 64, 10 * 64)), key=lambda r: r[1])
    print(f"peak f' - 1 = {mp.nstr(best[1] - 1, 8)} at eta ~ {mp.nstr(best[0], 6)}")
