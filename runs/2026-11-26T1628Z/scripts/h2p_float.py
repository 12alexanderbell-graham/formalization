"""High-precision floating plan for the H2+ certificate (run 2026-11-26T1628Z). NOT evidence: it only chooses
brackets for the exact-rational emulation (h2p_emulate.py).

Conventions (atomic units; nuclei of charge 1 at distance R; m = 0; sigma_g; printed sign of A, Madsen-Peek):
  k = p^2 = -E R^2 / 2  (E electronic energy, total energy = E + 1/R)
  eta: [(1 - eta^2) M']' + (k eta^2 - A) M = 0,   M regular at eta = 1 (and even: M'(0) = 0)
  xi : [(xi^2 - 1) L']' + (2 R xi - k xi^2 + A) L = 0, L regular at xi = 1, L -> 0 as xi -> infinity
Series:
  eta, s = 1 - eta:  M = sum b_n s^n, b_0 = 1,
     b_{n+1} = [(n(n+1) - k + A) b_n + 2k b_{n-1} - k b_{n-2}] / (2 (n+1)^2)
  xi, u = xi - 1:    L = sum c_n u^n, c_0 = 1,
     c_{n+1} = -[(n(n+1) + 2R - k + A) c_n + (2R - 2k) c_{n-1} - k c_{n-2}] / (2 (n+1)^2)
  xi about a regular point x0 (x = xi - x0):  L = sum d_n x^n,
     d_{n+2} = -[2 x0 (n+1)^2 d_{n+1} + (n(n+1) + N0) d_n + N1 d_{n-1} + N2 d_{n-2}] / ((x0^2 - 1)(n+1)(n+2))
     with N(x0 + x) = N0 + N1 x + N2 x^2, N0 = 2R x0 - k x0^2 + A, N1 = 2R - 2k x0, N2 = -k.
"""
import mpmath as mp

mp.mp.dps = 60
R = mp.mpf(2)


def eta_g(k, A, N=400):
    b = [mp.mpf(1)]
    for n in range(N):
        bm1 = b[n - 1] if n >= 1 else 0
        bm2 = b[n - 2] if n >= 2 else 0
        b.append(((n * (n + 1) - k + A) * b[n] + 2 * k * bm1 - k * bm2) / (2 * (n + 1) ** 2))
    return sum(n * b[n] for n in range(len(b))), b


def A_of_k(k):
    return mp.findroot(lambda A: eta_g(k, A)[0], mp.mpf('0.8117'))


def xi_frob(k, A, u, N=400):
    c = [mp.mpf(1)]
    for n in range(N):
        cm1 = c[n - 1] if n >= 1 else 0
        cm2 = c[n - 2] if n >= 2 else 0
        c.append(-((n * (n + 1) + 2 * R - k + A) * c[n] + (2 * R - 2 * k) * cm1 - k * cm2) / (2 * (n + 1) ** 2))
    L = sum(c[n] * u ** n for n in range(len(c)))
    dL = sum(n * c[n] * u ** (n - 1) for n in range(1, len(c)))
    return L, dL


def xi_step(k, A, x0, L0, dL0, h, N=400):
    N0 = 2 * R * x0 - k * x0 ** 2 + A
    N1 = 2 * R - 2 * k * x0
    N2 = -k
    d = [L0, dL0]
    for n in range(N):
        dm1 = d[n - 1] if n >= 1 else 0
        dm2 = d[n - 2] if n >= 2 else 0
        d.append(-(2 * x0 * (n + 1) ** 2 * d[n + 1] + (n * (n + 1) + N0) * d[n] + N1 * dm1 + N2 * dm2)
                 / ((x0 ** 2 - 1) * (n + 1) * (n + 2)))
    L = sum(d[n] * h ** n for n in range(len(d)))
    dL = sum(n * d[n] * h ** (n - 1) for n in range(1, len(d)))
    return L, dL


def shoot(k, X=12, ratio=mp.mpf('0.5')):
    A = A_of_k(k)
    x = mp.mpf(2)
    L, dL = xi_frob(k, A, x - 1)
    while x < X:
        h = min(ratio * (x - 1), X - x)
        L, dL = xi_step(k, A, x, L, dL, h)
        x += h
    return L, A


if __name__ == '__main__':
    lo, hi = mp.mpf('2.2052'), mp.mpf('2.2054')
    slo = mp.sign(shoot(lo)[0])
    for _ in range(80):
        mid = (lo + hi) / 2
        if mp.sign(shoot(mid)[0]) == slo:
            lo = mid
        else:
            hi = mid
    k = (lo + hi) / 2
    A = A_of_k(k)
    E = -2 * k / R ** 2
    print('sign of L at X=12 for k below the root:', slo)
    print('k* =', mp.nstr(k, 25))
    print('A* =', mp.nstr(A, 25))
    print('E electronic =', mp.nstr(E, 25), ' total =', mp.nstr(E + 1 / R, 25))
    print('p =', mp.nstr(mp.sqrt(k), 20))
