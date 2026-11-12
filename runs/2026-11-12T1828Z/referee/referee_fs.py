"""Independent referee numerics for Falkner-Skan reversed-flow (lower branch) wall shear.
f''' + f f'' + beta (1 - f'^2) = 0, f(0)=f'(0)=0, f'->1 with exponential (fast) approach.
High-order Taylor-series integrator in mpmath (own code), secant shooting on s = f''(0).
Far-field conditions: (A) f'(L)=1 ; (B) Robin condition killing the algebraic mode:
   f''(L) = (1-f'(L)) * (x + (1+2b)/x),  x = L - delta, delta = L - f(L)
Convergence checked in L, step h, Taylor order N and working precision.
"""
import sys
from mpmath import mp, mpf

def step(y, b, h, N):
    f0, p0, q0 = y
    a = [mpf(0)]*(N+1)
    a[0], a[1], a[2] = f0, p0, q0/2
    for k in range(0, N-2):
        # coefficient of t^k in f''' : (k+1)(k+2)(k+3) a_{k+3}
        s = mpf(0)
        for i in range(k+1):
            # f * f''   ; f'' coeff j: (j+1)(j+2) a_{j+2}
            j = k - i
            s -= a[i]*(j+1)*(j+2)*a[j+2]
            # beta f'^2 ; f' coeff m: (m+1) a_{m+1}
            s += b*(i+1)*a[i+1]*(j+1)*a[j+1]
        if k == 0:
            s -= b
        a[k+3] = s/((k+1)*(k+2)*(k+3))
    # evaluate f, f', f'' at t=h (Horner)
    f = p = q = mpf(0)
    for k in range(N, -1, -1):
        f = f*h + a[k]
    for k in range(N, 0, -1):
        p = p*h + k*a[k]
    for k in range(N, 1, -1):
        q = q*h + k*(k-1)*a[k]
    return (f, p, q)

def integrate(s, b, L, h, N, track=False):
    y = (mpf(0), mpf(0), mpf(s))
    n = int(round(L/h)); hh = mpf(L)/n
    pmin = pmax = mpf(0)
    for _ in range(n):
        y = step(y, b, hh, N)
        if track:
            pmin = min(pmin, y[1]); pmax = max(pmax, y[1])
        if abs(y[1]) > 50:
            break
    return (y, pmin, pmax) if track else y

def resid(s, b, L, h, N, cond):
    f, p, q = integrate(s, b, L, h, N)
    if cond == 'A':
        return p - 1
    x = L - (L - f)  # = f(L) ~ L - delta
    x = f
    return q - (1 - p)*(x + (1 + 2*b)/x)

def secant(s0, s1, b, L, h, N, cond, tol):
    r0 = resid(s0, b, L, h, N, cond); r1 = resid(s1, b, L, h, N, cond)
    for _ in range(60):
        s2 = s1 - r1*(s1 - s0)/(r1 - r0)
        s0, r0 = s1, r1
        s1, r1 = s2, resid(s2, b, L, h, N, cond)
        if abs(s1 - s0) < tol:
            return s1
    raise RuntimeError('no convergence')

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'main'
    WINDOWS = {
        '-0.15': ('-0.1334212379', '-0.1334212378'),
        '-0.17': ('-0.1142272391', '-0.1142272390'),
        '-0.18': ('-0.0976920602', '-0.0976920601'),
        '-0.19': ('-0.0713359061', '-0.0713359060'),
    }
    GUESS = {'-0.15': -0.1334, '-0.17': -0.1142, '-0.18': -0.0977, '-0.19': -0.0713}
    configs = [  # (dps, L, h, N, cond)
        (30, 10, mpf(1)/8, 24, 'A'), (30, 12, mpf(1)/8, 24, 'A'), (30, 14, mpf(1)/8, 24, 'A'),
        (30, 12, mpf(1)/8, 24, 'B'), (30, 14, mpf(1)/8, 24, 'B'),
        (40, 16, mpf(1)/16, 30, 'B'), (40, 16, mpf(1)/16, 30, 'A'),
    ]
    if mode == 'quick':
        configs = configs[:1]
    for bs, (lo, hi) in WINDOWS.items():
        print('beta =', bs, flush=True)
        vals = []
        for dps, L, h, N, cond in configs:
            mp.dps = dps
            b = mpf(bs)
            g = mpf(GUESS[bs])
            s = secant(g, g + mpf('1e-4'), b, L, h, N, cond, mpf(10)**(-dps+8))
            vals.append(s)
            print('  dps=%d L=%d h=%s N=%d cond=%s  s=%s' % (dps, L, h, N, cond, mp.nstr(s, 22)), flush=True)
        mp.dps = 40
        best = vals[-2]
        spread = max(abs(v - best) for v in vals[1:])
        lo, hi = mpf(lo), mpf(hi)
        inside = lo < best < hi
        print('  best=%s spread(excluding L=10)=%s inside=%s margin_lo=%s margin_hi=%s' % (
            mp.nstr(best, 20), mp.nstr(spread, 3), inside, mp.nstr(best - lo, 6), mp.nstr(hi - best, 6)), flush=True)
        (y, pmin, pmax) = integrate(best, mpf(bs), 16, mpf(1)/16, 30, track=True)
        print('  f\'min=%s f\'max=%s  at L=16: 1-f\'=%s f\'\'=%s ratio=%s' % (
            mp.nstr(pmin, 10), mp.nstr(pmax, 12), mp.nstr(1 - y[1], 5), mp.nstr(y[2], 5), mp.nstr(y[2]/(1 - y[1]), 6)), flush=True)
