"""Float study: Townes radial ground state Q'' + Q'/r - Q + Q^3 = 0, Q'(0) = 0.
Shooting on c = Q(0): overshoot (Q hits 0 with Q' < 0) vs undershoot (Q' > 0 while Q > 0).
Bisection in mpmath (series start, then taylor ODE solver)."""
import mpmath as mp
import sys

mp.mp.dps = 40


def series(c, r, n=12):
    # Q = sum a_k r^{2k}: (2k)^2 a_k... from (r Q')' = r(Q - Q^3)
    # coefficients of Q in powers r^{2k}: a_{k+1} (2k+2)^2 = [Q - Q^3]_{k}
    a = [mp.mpf(c)]
    for k in range(n):
        # cube coefficient k
        cube = mp.mpf(0)
        for i in range(k + 1):
            for j in range(k + 1 - i):
                cube += a[i] * a[j] * a[k - i - j]
        a.append((a[k] - cube) / (2 * k + 2) ** 2)
    Q = sum(a[k] * r ** (2 * k) for k in range(len(a)))
    P = sum(2 * k * a[k] * r ** (2 * k - 1) for k in range(1, len(a)))
    return Q, P


def shoot(c, rmax=25):
    r0 = mp.mpf(1) / 20
    Q0, P0 = series(c, r0)
    f = mp.odefun(lambda r, y: [y[1], -y[1] / r + y[0] - y[0] ** 3], r0, [Q0, P0])
    r = r0
    h = mp.mpf(1) / 10
    while r < rmax:
        r += h
        Q, P = f(r)
        if Q < 0:
            return +1, r
        if P > 0:
            return -1, r
    return 0, r


if __name__ == "__main__":
    lo, hi = mp.mpf("2.2"), mp.mpf("2.21")
    print(shoot(lo), shoot(hi))
    for it in range(int(sys.argv[1]) if len(sys.argv) > 1 else 20):
        mid = (lo + hi) / 2
        s, r = shoot(mid)
        if s > 0:
            hi = mid
        elif s < 0:
            lo = mid
        else:
            print("undecided", mid, r)
            break
        print(it, mp.nstr(lo, 15), mp.nstr(hi, 15), s, mp.nstr(r, 4))
