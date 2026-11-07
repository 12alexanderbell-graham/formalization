#!/usr/bin/env python3
"""Referee shooting for the Townes radial ODE (run 2026-11-07T0628Z, referee_exists.md).

theta'' + theta'/r - theta + theta^3 = 0, theta(0) = c, theta'(0) = 0.
Floating multiprecision (mpmath), NOT rigorous.

Method A (own Taylor stepper):
  * power series at r = 0: theta = sum a_{2k} r^{2k}; (k+2)^2 a_{k+2} = a_k - [theta^3]_k,
    summed to r0 = 1/4;
  * fixed-step Taylor integrator in t = r - r_c from  (r_c + t) theta'' + theta' = (r_c + t) g,
    g = theta - theta^3:
      u_{n+2} = (r_c g_n + g_{n-1} - (n+1)^2 u_{n+1}) / (r_c (n+2)(n+1));
  * classification: UNDER if phi > 0 while theta > 0, OVER if theta < 0 while phi < 0
    (checked at step ends; the step is small compared with the event scales);
  * bisection on c in [2.2062008646, 2.2062008647].
Method B (independent code path): mpmath.odefun (its own adaptive Taylor method) started at
  r0 = 1/4 from the same series, used only to classify the two bracket endpoints and to
  shoot the bisection midpoint from Method A.
Usage: python3 referee_shoot.py [dps] [h] [order] [nbisect]
"""
import sys
import mpmath as mp

DPS = int(sys.argv[1]) if len(sys.argv) > 1 else 40
H = sys.argv[2] if len(sys.argv) > 2 else None
ORDER = int(sys.argv[3]) if len(sys.argv) > 3 else 30
NBIS = int(sys.argv[4]) if len(sys.argv) > 4 else 40
mp.mp.dps = DPS
H = mp.mpf(H) if H is not None else mp.mpf(1) / 20
R0 = mp.mpf(1) / 4
RMAX = mp.mpf(80)


def cube_coeffs(a, n):
    sq = [mp.fsum(a[i] * a[k - i] for i in range(k + 1)) for k in range(n)]
    return [mp.fsum(sq[i] * a[k - i] for i in range(k + 1)) for k in range(n)]


def series_at_zero(c, r, nterms=120):
    """theta, phi at r from the even power series in s = r^2."""
    a = [mp.mpf(c)]
    # a_k is the coefficient of s^k = r^(2k); 4(k+1)^2 a_{k+1} = a_k - (a^3)_k
    for k in range(nterms):
        cub = mp.fsum(
            mp.fsum(a[i] * a[j] * a[k - i - j] for j in range(k - i + 1)) for i in range(k + 1))
        a.append((a[k] - cub) / (4 * (k + 1) ** 2))
    s = r * r
    th = mp.fsum(a[k] * s ** k for k in range(len(a)))
    ph = mp.fsum(2 * k * a[k] * r ** (2 * k - 1) for k in range(1, len(a)))
    tail = abs(a[-1] * s ** (len(a) - 1))
    return th, ph, tail


def taylor_step(rc, th, ph, h, N):
    u = [th, ph]
    g = []
    for n in range(N - 1):
        # g_n needs u_0..u_n
        cub = cube_coeffs(u, n + 1)[n]
        g.append(u[n] - cub)
        gm1 = g[n - 1] if n >= 1 else mp.mpf(0)
        u.append((rc * g[n] + gm1 - (n + 1) ** 2 * u[n + 1]) / (rc * (n + 2) * (n + 1)))
    th1 = mp.fsum(u[n] * h ** n for n in range(len(u)))
    ph1 = mp.fsum(n * u[n] * h ** (n - 1) for n in range(1, len(u)))
    return th1, ph1


def shoot(c, h=H, N=ORDER):
    th, ph, _ = series_at_zero(c, R0)
    r = R0
    while r < RMAX:
        th, ph = taylor_step(r, th, ph, h, N)
        r += h
        if th > 0 and ph > 0:
            return 'UNDER', r
        if th < 0 and ph < 0:
            return 'OVER', r
    return 'NONE', r


def shoot_odefun(c, rmax=RMAX):
    th0, ph0, _ = series_at_zero(c, R0)
    f = mp.odefun(lambda r, y: [y[1], -y[1] / r + y[0] - y[0] ** 3], R0, [th0, ph0])
    r = R0
    step = mp.mpf(1) / 10
    while r < rmax:
        r += step
        th, ph = f(r)
        if th > 0 and ph > 0:
            return 'UNDER', r
        if th < 0 and ph < 0:
            return 'OVER', r
    return 'NONE', r


if __name__ == '__main__':
    lo, hi = mp.mpf('2.2062008646'), mp.mpf('2.2062008647')
    _, _, tail = series_at_zero(lo, R0)
    print(f'dps={DPS} h={H} order={ORDER} r0={R0} series tail ~ {mp.nstr(tail, 3)}')
    for c in (lo, hi):
        print('A', mp.nstr(c, 12), *shoot(c))
    assert shoot(lo)[0] == 'UNDER' and shoot(hi)[0] == 'OVER'
    for _ in range(NBIS):
        mid = (lo + hi) / 2
        ev, _r = shoot(mid)
        if ev == 'UNDER':
            lo = mid
        elif ev == 'OVER':
            hi = mid
        else:
            raise SystemExit(f'no event at {mid}')
    print('A bracket for Q(0):', mp.nstr(lo, 25), mp.nstr(hi, 25))
    print('A Q(0) ~', mp.nstr((lo + hi) / 2, 20))
    print('A distance to 2.2062008646:', mp.nstr(lo - mp.mpf('2.2062008646'), 6),
          ' to 2.2062008647:', mp.nstr(mp.mpf('2.2062008647') - hi, 6))
    if True:  # Method B cross-check
        mp.mp.dps = min(DPS, 30)
        for c in (mp.mpf('2.2062008646'), mp.mpf('2.2062008647'), lo - mp.mpf('1e-15'),
                  hi + mp.mpf('1e-15')):
            print('B odefun', mp.nstr(c, 20), *shoot_odefun(c))
