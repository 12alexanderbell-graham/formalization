"""Independent high-precision computation of the turning points of the regular
solution W of w'' + (2/s) w' + e^w = 0, w(0)=0.

Method: power series of W in x = s^2 near 0 (to reach s0), then a high-order
Taylor-series integrator for the homology system in t = log s:
    u' = u(3 - u - v),  v' = v(u - 1),   lambda = u v,
turning points = zeros of y = v - 2, where lambda = 2u.
Error estimate: rerun with different (dps, order, step, s0) and compare.

usage: python3 turning_points.py DPS ORDER STEP S0 KMAX
"""
import sys
import mpmath as mp


def run(dps, order, h, s0, kmax):
    mp.mp.dps = dps
    h = mp.mpf(h)
    s0 = mp.mpf(s0)
    # series W = sum a_n x^n, E = e^W = sum b_n x^n, x = s^2
    # (s^2 W')' = -s^2 e^W  =>  2n(2n+1) a_n = -b_{n-1};  n b_n = sum_{k=1}^n k a_k b_{n-k}
    N = 400
    a = [mp.mpf(0)] * (N + 1)
    b = [mp.mpf(0)] * (N + 1)
    b[0] = mp.mpf(1)
    for n in range(1, N + 1):
        a[n] = -b[n - 1] / (2 * n * (2 * n + 1))
        b[n] = mp.fsum(k * a[k] * b[n - k] for k in range(1, n + 1)) / n
    x = s0 ** 2
    W = mp.fsum(a[n] * x ** n for n in range(N + 1))
    sWp = mp.fsum(2 * n * a[n] * x ** n for n in range(1, N + 1))  # s W'(s)
    tail = abs(a[N] * x ** N)
    u = s0 ** 2 * mp.e ** W / (-sWp)
    v = -sWp
    t = mp.log(s0)

    def taylor(u0, v0):
        U = [u0]
        V = [v0]
        for n in range(order):
            uv = mp.fsum(U[i] * V[n - i] for i in range(n + 1))
            uu = mp.fsum(U[i] * U[n - i] for i in range(n + 1))
            U.append((3 * U[n] - uu - uv) / (n + 1))
            V.append((uv - V[n]) / (n + 1))
        return U, V

    def ev(c, tau):
        r = mp.mpf(0)
        for cc in reversed(c):
            r = r * tau + cc
        return r

    def dev(c, tau):
        r = mp.mpf(0)
        for i in range(len(c) - 1, 0, -1):
            r = r * tau + i * c[i]
        return r

    out = []
    while len(out) <= kmax:
        U, V = taylor(u, v)
        un = ev(U, h)
        vn = ev(V, h)
        y0, y1 = v - 2, vn - 2
        if y0 == 0 or (y0 > 0) != (y1 > 0):
            # root of V(tau) - 2 in [0, h]: bisection then Newton
            lo, hi = mp.mpf(0), h
            for _ in range(40):
                mid = (lo + hi) / 2
                if ((ev(V, mid) - 2) > 0) == (y0 > 0):
                    lo = mid
                else:
                    hi = mid
            tau = (lo + hi) / 2
            for _ in range(60):
                d = (ev(V, tau) - 2) / dev(V, tau)
                tau -= d
                if abs(d) < mp.mpf(10) ** (-dps + 5):
                    break
            uz = ev(U, tau)
            out.append((t + tau, uz))
        u, v, t = un, vn, t + h
    return out, tail


if __name__ == "__main__":
    dps, order, h, s0, kmax = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4], int(sys.argv[5])
    out, tail = run(dps, order, h, s0, kmax)
    mp.mp.dps = dps
    print("series tail at s0:", mp.nstr(tail, 5))
    for k, (tz, uz) in enumerate(out):
        print(k, mp.nstr(tz, dps - 5), mp.nstr(uz, dps - 5))
