"""High-order Taylor integrator for w'' + (2/s) w' + e^w = 0, w(0)=0, w'(0)=0.
Finds zeros of g(s) = 2 + s w'(s) (turning points of lambda = s^2 e^w) and lambda there.
Usage: python3 taylor.py DPS ORDER STEPFRAC
"""
import sys
from mpmath import mp, mpf, exp, nstr

DPS = int(sys.argv[1]) if len(sys.argv) > 1 else 50
N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
FRAC = mpf(sys.argv[3]) if len(sys.argv) > 3 else mpf('0.1')
mp.dps = DPS

def series_at_zero(N):
    # s w'' + 2 w' + s e^w = 0 ; a_{n+1} = -e_{n-1}/((n+1)(n+2))
    a = [mpf(0)] * (N + 2)
    e = [mpf(0)] * (N + 2)
    e[0] = mpf(1)
    for n in range(1, N + 1):
        # a_{n+1} needs e_{n-1}
        a[n + 1] = -e[n - 1] / ((n + 1) * (n + 2))
        # e_n = (1/n) sum_{k=1}^n k a_k e_{n-k}
        e[n] = sum(k * a[k] * e[n - k] for k in range(1, n + 1)) / n
    return a[:N + 1]

def series_at(s0, w0, w1, N):
    a = [mpf(0)] * (N + 2)
    e = [mpf(0)] * (N + 2)
    a[0], a[1] = w0, w1
    e[0] = exp(w0)
    for n in range(0, N - 1):
        if n >= 1:
            e[n] = sum(k * a[k] * e[n - k] for k in range(1, n + 1)) / n
        em1 = e[n - 1] if n >= 1 else mpf(0)
        a[n + 2] = -((n + 1) * (n + 2) * a[n + 1] + s0 * e[n] + em1) / (s0 * (n + 1) * (n + 2))
    return a[:N]

def ev(a, h):
    p = mpf(0); dp = mpf(0)
    for k in range(len(a) - 1, -1, -1):
        dp = dp * h + p if k < len(a) - 1 else dp
        p = p * h + a[k]
    # recompute derivative cleanly
    dp = mpf(0)
    for k in range(len(a) - 1, 0, -1):
        dp = dp * h + k * a[k]
    return p, dp

def run(smax=mpf(200000), nturn=6):
    # start: series at 0 up to s = 0.5
    a0 = series_at_zero(N)
    s = mpf('0.5')
    w, wp = ev(a0, s)
    g = lambda s, wp: 2 + s * wp
    out = []
    while s < smax and len(out) < nturn:
        h = FRAC * s
        a = series_at(s, w, wp, N)
        w2, wp2 = ev(a, h)
        g1, g2 = g(s, wp), g(s + h, wp2)
        if g1 * g2 < 0:
            # Newton on G(x) = 2 + (s+x) W'(x)
            x = h * g1 / (g1 - g2)
            for _ in range(200):
                wx, wpx = ev(a, x)
                # W''(x)
                wpp = mpf(0)
                for k in range(len(a) - 1, 1, -1):
                    wpp = wpp * x + k * (k - 1) * a[k]
                G = 2 + (s + x) * wpx
                dG = wpx + (s + x) * wpp
                dx = G / dG
                x -= dx
                if abs(dx) < mpf(10) ** (-DPS + 5) * (s + 1):
                    break
            wx, wpx = ev(a, x)
            z = s + x
            lam = z ** 2 * exp(wx)
            out.append((z, lam))
        s, w, wp = s + h, w2, wp2
    return out

if __name__ == '__main__':
    res = run()
    for i, (z, lam) in enumerate(res):
        print(i, nstr(z, 40), nstr(lam, 40))
