"""Referee (run 2026-11-11T1228Z), Method B + IVP study, multiprecision.

Own Taylor-series integrator (mpmath, 40 digits, order 36, step 1/16) for
    f''' = -f f'' - beta (1 - f'^2),  beta = -1988/10000,  f(0) = f'(0) = 0, f''(0) = alpha.
(B) alpha of the reversed branch = root (secant) of the parabolic-cylinder tail residual at eta = L,
        R(alpha) = f''(L) - (1 - f'(L)) D_{nu+1}(x)/D_nu(x),  x = f(L),  nu = -1 - 2 beta,
    for L = 7..13 (no overshoot/undershoot classification is used).
(C) the IVP with Fazio's printed alpha = -0.005158: where f' first exceeds 1, by how much, and what the
    trajectory does afterwards (global existence, limit of f').

Usage: nice python3 rev_taylor.py
"""
import mpmath as mp

mp.mp.dps = 40
BETA = mp.mpf(-1988) / 10000
NU = -1 - 2 * BETA
ORDER = 36
H = mp.mpf(1) / 16


def taylor_step(f0, p0, q0, h=H, n=ORDER):
    """Taylor coefficients a_k of f about the current point; returns (f, f', f'') at +h."""
    a = [mp.mpf(0)] * (n + 1)
    a[0], a[1], a[2] = f0, p0, q0 / 2
    for k in range(0, n - 2):
        # coefficient of t^k in f f'' and in f'^2
        s1 = mp.fsum(a[i] * (k - i + 2) * (k - i + 1) * a[k - i + 2] for i in range(k + 1))
        s2 = mp.fsum((i + 1) * a[i + 1] * (k - i + 1) * a[k - i + 1] for i in range(k + 1))
        rhs = -s1 - BETA * ((1 if k == 0 else 0) - s2)
        a[k + 3] = rhs / ((k + 1) * (k + 2) * (k + 3))
    f = mp.fsum(a[k] * h ** k for k in range(n + 1))
    p = mp.fsum(k * a[k] * h ** (k - 1) for k in range(1, n + 1))
    q = mp.fsum(k * (k - 1) * a[k] * h ** (k - 2) for k in range(2, n + 1))
    return f, p, q


def integrate(alpha, L, record=None):
    y = (mp.mpf(0), mp.mpf(0), mp.mpf(alpha))
    nsteps = int(mp.nint(L / H))
    for i in range(nsteps):
        y = taylor_step(*y)
        if record is not None:
            record((i + 1) * H, y)
    return y


def tail_residual(alpha, L):
    f, p, q = integrate(alpha, L)
    r = mp.pcfd(NU + 1, f) / mp.pcfd(NU, f)
    return q - (1 - p) * r


def solve_tail(L, a0, a1):
    r0, r1 = tail_residual(a0, L), tail_residual(a1, L)
    for _ in range(40):
        a2 = a1 - r1 * (a1 - a0) / (r1 - r0)
        a0, r0, a1 = a1, r1, a2
        r1 = tail_residual(a1, L)
        if abs(a1 - a0) < mp.mpf(10) ** (-30):
            break
    return a1


if __name__ == "__main__":
    print("== (B) reversed branch by tail matching ==", flush=True)
    for L in [7, 8, 9, 10, 11, 12, 13]:
        a = solve_tail(mp.mpf(L), mp.mpf("-0.005157"), mp.mpf("-0.0051575"))
        print(f"L={L:3d}  f''(0) = {mp.nstr(a, 22)}", flush=True)
    # step-size check at L = 10
    H = mp.mpf(1) / 32
    a = solve_tail(mp.mpf(10), mp.mpf("-0.005157"), mp.mpf("-0.0051575"))
    print(f"L= 10, h=1/32: f''(0) = {mp.nstr(a, 22)}", flush=True)
    H = mp.mpf(1) / 16
    alpha_true = a
    lo, hi = mp.mpf("-0.00515743"), mp.mpf("-0.00515741")
    print(f"in window (-0.00515743, -0.00515741): {lo < alpha_true < hi}; margins "
          f"{mp.nstr(alpha_true - lo, 6)} (lower), {mp.nstr(hi - alpha_true, 6)} (upper)")
    K = mp.mpf(2500) / 497
    print(f"scaled A = sqrt(K) f''(0) = {mp.nstr(mp.sqrt(K) * alpha_true, 20)}; window in A: "
          f"({mp.nstr(mp.sqrt(K) * lo, 14)}, {mp.nstr(mp.sqrt(K) * hi, 14)}); chains A_over = -0.011567117 -> "
          f"f''(0) = {mp.nstr(mp.mpf('-0.011567117') / mp.sqrt(K), 14)}, A_slow = -0.011567073 -> "
          f"f''(0) = {mp.nstr(mp.mpf('-0.011567073') / mp.sqrt(K), 14)}")

    print("== class check along the true reversed profile (alpha from L=10) ==", flush=True)
    rows = []
    integrate(alpha_true, 10, record=lambda t, y: rows.append((t, y)))
    pmin = min(rows, key=lambda r: r[1][1])
    print(f"min f' on grid = {mp.nstr(pmin[1][1], 8)} at eta = {mp.nstr(pmin[0], 6)}; "
          f"max f' on [0,10] grid = {mp.nstr(max(r[1][1] for r in rows), 25)}")
    print("1 - f' > 0 at all grid points eta <= 10:", all(1 - r[1][1] > 0 for r in rows))
    for t, (f, p, q) in rows:
        if t in (2, 4, 6, 8, 10):
            print(f"  eta={mp.nstr(t, 3):>4} 1-f'={mp.nstr(1 - p, 6):>12} f''={mp.nstr(q, 6):>12} "
                  f"f''/(1-f')={mp.nstr(q / (1 - p), 6)}")

    print("== (C) IVP with printed alpha = -0.005158 ==", flush=True)
    for alpha_s in ["-0.005158", "-0.0051575", "-0.005157"]:
        alpha = mp.mpf(alpha_s)
        y = (mp.mpf(0), mp.mpf(0), alpha)
        t = mp.mpf(0)
        first = None
        pmax, tmax = mp.mpf(-10), None
        log = []
        while t < 200:
            y = taylor_step(*y)
            t += H
            if first is None and y[1] > 1:
                first = t
            if y[1] > pmax:
                pmax, tmax = y[1], t
            if mp.nint(t * 16) % 160 == 0:
                log.append((t, y))
            if abs(y[1]) > 1e6:
                print("  blow-up?", t)
                break
        print(f"alpha={alpha_s}: first grid eta with f'>1: {mp.nstr(first, 6) if first else None}; "
              f"max f' on [0,200] = 1 + {mp.nstr(pmax - 1, 6)} at eta = {mp.nstr(tmax, 6)}", flush=True)
        for (tt, (f, p, q)) in log:
            if tt in (5, 10, 20, 30, 50, 100, 150, 200):
                print(f"    eta={mp.nstr(tt, 4):>5} f'-1={mp.nstr(p - 1, 6):>13} f''={mp.nstr(q, 6):>13} "
                      f"(f'-1)*(eta-delta)^(-2 beta) = {mp.nstr((p - 1) * (tt - 2.3851678) ** (-2 * BETA), 6)}")
