"""Independent high-precision computation of the turning values of the radial Gelfand branch.

System in t = log s:  u' = u(3 - u - v),  v' = v(u - 1),  lambda = u v.
Turning points = zeros of v - 2 (v = -s W').  Taylor-series integrator of fixed order N,
fixed step h, all in mpmath at `dps` digits.  Error estimate: compare two runs
(different order/step/precision).
"""
import sys
import mpmath as mp


def initial(s0, nterms):
    # W = sum a_n z^n, E = e^W = sum e_n z^n, z = s^2.
    a = [mp.mpf(0)] * (nterms + 1)
    e = [mp.mpf(0)] * (nterms + 1)
    e[0] = mp.mpf(1)
    for n in range(1, nterms + 1):
        # (2n)(2n+1) a_n = -e_{n-1}
        a[n] = -e[n - 1] / ((2 * n) * (2 * n + 1))
        e[n] = sum(k * a[k] * e[n - k] for k in range(1, n + 1)) / n
    z = s0 ** 2
    W = sum(a[n] * z ** n for n in range(nterms + 1))
    Wp = sum(2 * n * a[n] * s0 ** (2 * n - 1) for n in range(1, nterms + 1))
    u = s0 * mp.e ** W / (-Wp)
    v = -s0 * Wp
    tail = abs(a[nterms] * z ** nterms)
    return u, v, tail


def taylor(u0, v0, N):
    U = [u0] + [mp.mpf(0)] * N
    V = [v0] + [mp.mpf(0)] * N
    for n in range(N):
        uu = sum(U[i] * U[n - i] for i in range(n + 1))
        uv = sum(U[i] * V[n - i] for i in range(n + 1))
        U[n + 1] = (3 * U[n] - uu - uv) / (n + 1)
        V[n + 1] = (uv - V[n]) / (n + 1)
    return U, V


def ev(C, x):
    r = mp.mpf(0)
    for c in reversed(C):
        r = r * x + c
    return r


def dev(C, x):
    r = mp.mpf(0)
    for k in range(len(C) - 1, 0, -1):
        r = r * x + k * C[k]
    return r


def run(dps, N, h, s0, kmax):
    mp.mp.dps = dps
    h = mp.mpf(h)
    s0 = mp.mpf(s0)
    u, v, tail = initial(s0, 60)
    t = mp.log(s0)
    out = []
    y_prev = v - 2
    while len(out) < kmax + 1:
        U, V = taylor(u, v, N)
        Y = list(V)
        Y[0] -= 2
        un, vn = ev(U, h), ev(V, h)
        yn = vn - 2
        if y_prev == 0 or (y_prev < 0) != (yn < 0):
            # root of Y in (0, h]: Newton from linear interpolation
            x = h * y_prev / (y_prev - yn)
            for _ in range(100):
                dx = ev(Y, x) / dev(Y, x)
                x -= dx
                if abs(dx) < mp.mpf(10) ** (-dps + 3):
                    break
            uz, vz = ev(U, x), ev(V, x)
            out.append((t + x, uz * vz))
        u, v, t, y_prev = un, vn, t + h, yn
    return out


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    A = run(60, 40, "0.05", "0.001", kmax)
    B = run(70, 48, "0.04", "0.0005", kmax)
    mp.mp.dps = 60
    L = -mp.e ** (-mp.pi / mp.sqrt(7))
    print("limit -exp(-pi/sqrt7) =", mp.nstr(L, 30))
    print("k  zeta_k  lambda_k-2  |A-B| on lambda  quotient q_k=(l_{k+1}-2)/(l_k-2)  q_k-L  (q_k-L)/(l_k-2)")
    for k in range(kmax + 1):
        tz, lz = A[k]
        err = abs(lz - B[k][1])
        line = f"{k:2d} {mp.nstr(mp.e**tz, 20):>24} {mp.nstr(lz - 2, 25):>34} {mp.nstr(err, 3):>9}"
        if k < kmax:
            q = (A[k + 1][1] - 2) / (lz - 2)
            line += f"  {mp.nstr(q, 25)}  {mp.nstr(q - L, 6)}  {mp.nstr((q - L) / (lz - 2), 6)}"
        print(line)
