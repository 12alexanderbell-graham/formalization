"""Referee recomputation of the Falkner-Skan separation value beta*.

Method (deliberately different from the run's overshoot/slow bisection in scaled variables):
  * unscaled beta form  f''' + f f'' + beta (1 - f'^2) = 0,  f(0)=f'(0)=f''(0)=0;
  * integrate with mpmath.odefun (mpmath's own adaptive Taylor integrator) to eta_inf;
  * match to the exact decaying (Gaussian) mode of the linearised tail equation
        g'' + x g' - 2 beta g = 0,   g = 1 - f',  x = f(eta_inf)  (f = eta - delta + exp. small),
    whose decaying solution is g = exp(-x^2/4) D_nu(x), nu = -1 - 2 beta, so
        -g'/g = D_{nu+1}(x) / D_nu(x)     (parabolic cylinder functions, mpmath.pcfd);
  * Phi(beta) = q(eta_inf) - (1 - p(eta_inf)) * D_{nu+1}(x)/D_nu(x); secant iteration on beta.
The residual of the neglected nonlinear term beta g^2 is O(g) ~ exp(-x^2/2) relative.

Usage: nice python3 beta_star_odefun.py [dps] [eta_inf ...]
"""
import sys
import time
import mpmath as mp


def shoot(beta, eta_inf):
    beta = mp.mpf(beta)

    def F(t, y):
        f, p, q = y
        return [p, q, -f * q - beta * (1 - p * p)]

    sol = mp.odefun(F, 0, [mp.mpf(0), mp.mpf(0), mp.mpf(0)])
    f, p, q = sol(mp.mpf(eta_inf))
    return f, p, q


def phi(beta, eta_inf):
    f, p, q = shoot(beta, eta_inf)
    nu = -1 - 2 * mp.mpf(beta)
    x = f
    r = mp.pcfd(nu + 1, x) / mp.pcfd(nu, x)
    return q - (1 - p) * r, (f, p, q, r)


def solve(eta_inf, b0, b1, tol):
    p0, _ = phi(b0, eta_inf)
    p1, info = phi(b1, eta_inf)
    for it in range(40):
        b2 = b1 - p1 * (b1 - b0) / (p1 - p0)
        b0, p0 = b1, p1
        b1 = b2
        p1, info = phi(b1, eta_inf)
        if abs(b1 - b0) < tol:
            break
    return b1, info


if __name__ == "__main__":
    dps = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    etas = [float(a) for a in sys.argv[2:]] or [7, 8, 9, 10]
    mp.mp.dps = dps
    tol = mp.mpf(10) ** (-(dps - 8))
    b0, b1 = mp.mpf("-0.19883"), mp.mpf("-0.19884")
    for e in etas:
        t0 = time.time()
        b, (f, p, q, r) = solve(e, b0, b1, tol)
        print(f"eta_inf={e:5}: beta*={mp.nstr(b, dps - 6)}  x=f={mp.nstr(f, 12)}  1-p={mp.nstr(1 - p, 5)}"
              f"  q/(1-p)={mp.nstr(r, 10)}  [{time.time() - t0:.0f}s]", flush=True)
        b0, b1 = b, b + mp.mpf(10) ** (-14)
    lo, hi = mp.mpf("-0.1988377351"), mp.mpf("-0.1988377350")
    print("in window (-0.1988377351, -0.1988377350):", lo < b < hi,
          " margins:", mp.nstr(b - lo, 6), mp.nstr(hi - b, 6))
