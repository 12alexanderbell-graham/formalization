"""Wall shear alpha = f''(0) of the two Gaussian-tail branches near separation, to compare with
printed tables (e.g. f''(0) = 0.005225 at beta = -0.1988; Fazio 2012's +-6.61e-6 at
beta = -0.198837723795).  Same tail matching as beta_star_odefun.py, secant on alpha.

Usage: nice python3 wall_shear_check.py beta [eta_inf] [dps]
"""
import sys
import mpmath as mp


def phi(beta, alpha, eta_inf):
    beta, alpha = mp.mpf(beta), mp.mpf(alpha)

    def F(t, y):
        f, p, q = y
        return [p, q, -f * q - beta * (1 - p * p)]

    f, p, q = mp.odefun(F, 0, [mp.mpf(0), mp.mpf(0), alpha])(mp.mpf(eta_inf))
    nu = -1 - 2 * beta
    return q - (1 - p) * mp.pcfd(nu + 1, f) / mp.pcfd(nu, f)


def branch(beta, a0, a1, eta_inf, tol):
    p0, p1 = phi(beta, a0, eta_inf), phi(beta, a1, eta_inf)
    for _ in range(60):
        a2 = a1 - p1 * (a1 - a0) / (p1 - p0)
        a0, p0, a1 = a1, p1, a2
        p1 = phi(beta, a1, eta_inf)
        if abs(a1 - a0) < tol:
            break
    return a1


if __name__ == "__main__":
    beta = mp.mpf(sys.argv[1])
    eta_inf = float(sys.argv[2]) if len(sys.argv) > 2 else 11
    mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    bstar = mp.mpf("-0.19883773504667754688904713181526")
    guess = mp.sqrt(max(beta - bstar, mp.mpf(10) ** -24) / mp.mpf("1.4"))
    tol = mp.mpf(10) ** (-(mp.mp.dps - 8))
    up = branch(beta, guess, guess * mp.mpf("1.01"), eta_inf, tol)
    lo = branch(beta, -guess, -guess * mp.mpf("1.01"), eta_inf, tol)
    print(f"beta={mp.nstr(beta, 15)}  beta-beta*={mp.nstr(beta - bstar, 6)}  "
          f"f''(0) upper={mp.nstr(up, 12)}  lower={mp.nstr(lo, 12)}  "
          f"(beta-beta*)/alpha^2={mp.nstr((beta - bstar) / up ** 2, 8)}", flush=True)
