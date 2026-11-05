"""Floating-point reference for the Lane-Emden n = 3 constants (guide only, not a certificate).
Run 2026-11-05T0028Z. theta'' + (2/xi) theta' + theta^3 = 0, theta(0) = 1, theta'(0) = 0.
Series at 0: theta = sum a_k xi^(2k), 2k(2k+1) a_k = -[theta^3]_(k-1); then mpmath ODE solver."""
import mpmath as mp

mp.mp.dps = 40
N = 40


def series(N):
    a = [mp.mpf(0)] * N
    a[0] = mp.mpf(1)
    for k in range(1, N):
        sq = [sum(a[i] * a[j - i] for i in range(j + 1)) for j in range(k)]
        c3 = [sum(sq[i] * a[j - i] for i in range(j + 1)) for j in range(k)]
        a[k] = -c3[k - 1] / (2 * k * (2 * k + 1))
    return a


if __name__ == "__main__":
    a = series(N)
    print("series", [mp.nstr(x, 10) for x in a[:6]])
    x0 = mp.mpf(1) / 4
    th = sum(a[k] * x0 ** (2 * k) for k in range(N))
    dth = sum(2 * k * a[k] * x0 ** (2 * k - 1) for k in range(1, N))
    sol = mp.odefun(lambda x, y: [y[1], -2 * y[1] / x - y[0] ** 3], x0, [th, dth])
    z = mp.findroot(lambda x: sol(x)[0], 6.9)
    om = -z ** 2 * sol(z)[1]
    print("xi1", mp.nstr(z, 20))
    print("omega3", mp.nstr(om, 20))
    print("rho_c/rho_mean", mp.nstr(z ** 3 / (3 * om), 20))
