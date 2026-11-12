# Method A: own Taylor-series integrator (order N, fixed step) for w'' + (2/x) w' + e^w = 0, w(0)=w'(0)=0.
# Recurrence for expansion about x = a (xi = a + h):
#   a (n+1)(n+2) w_{n+2} = -(n+1)(n+2) w_{n+1} - a E_n - E_{n-1},   E = e^w,  E_k = (1/k) sum_{j=1}^k j w_j E_{k-j}
# At a = 0 this reduces to w_{n+1} = -E_{n-1} / ((n+1)(n+2)) (regular centre).
import mpmath as mp
mp.mp.dps = 50
N = 60  # Taylor order

def coeffs(a, w0, w1, N=N):
    w = [mp.mpf(w0), mp.mpf(w1)] + [mp.mpf(0)] * (N + 1)
    E = [mp.e ** w[0]] + [mp.mpf(0)] * (N + 1)
    if a == 0:
        # w_{n+1} from E_{n-1}; w1 = 0
        for n in range(1, N):
            k = n - 1
            if k >= 1:
                E[k] = sum(j * w[j] * E[k - j] for j in range(1, k + 1)) / k
            w[n + 1] = -E[n - 1] / ((n + 1) * (n + 2))
        return w[:N + 1]
    for n in range(0, N - 1):
        if n >= 1:
            E[n] = sum(j * w[j] * E[n - j] for j in range(1, n + 1)) / n
        Em1 = E[n - 1] if n >= 1 else 0
        w[n + 2] = (-(n + 1) * (n + 2) * w[n + 1] - a * E[n] - Em1) / (a * (n + 1) * (n + 2))
    return w[:N + 1]

def step(a, w0, w1, h):
    c = coeffs(a, w0, w1)
    W = sum(c[k] * h ** k for k in range(len(c)))
    P = sum(k * c[k] * h ** (k - 1) for k in range(1, len(c)))
    return W, P

def state(x, h=mp.mpf('0.05')):
    """integrate from 0 to x with fixed step h (last step shortened)"""
    x = mp.mpf(x)
    a, W, P = mp.mpf(0), mp.mpf(0), mp.mpf(0)
    while a < x:
        hh = min(h, x - a)
        W, P = step(a, W, P, hh)
        a += hh
    return W, P

def F(x, h=mp.mpf('0.05')):
    W, P = state(x, h)
    return mp.e ** W - P ** 2 / 2   # dm/dx = x^2 e^{w/2} (e^w - w'^2/2)/sqrt(4 pi)

def m_of(x, W, P):
    return x ** 2 * (-P) * mp.e ** (W / 2) / mp.sqrt(4 * mp.pi)

if __name__ == '__main__':
    for h in [mp.mpf('0.1'), mp.mpf('0.05')]:
        xi = mp.findroot(lambda x: F(x, h), mp.mpf('6.45'), solver='secant', tol=mp.mpf(10) ** -40)
        W, P = state(xi, h)
        print('h =', h)
        print(' xi1      =', mp.nstr(xi, 30))
        print(' m(xi1)   =', mp.nstr(m_of(xi, W, P), 30))
        print(' contrast =', mp.nstr(mp.e ** (-W), 30))
        print(' w, w\'    =', mp.nstr(W, 25), mp.nstr(P, 25))
    # sign scan of F on (0, 60] to locate all zeros of dm/dx
    mp.mp.dps = 30
    a, W, P = mp.mpf(0), mp.mpf(0), mp.mpf(0)
    h = mp.mpf('0.02'); prevF = None; zs = []
    while a < 400:
        W, P = step(a, W, P, h); a += h
        f = mp.e ** W - P ** 2 / 2
        if prevF is not None and prevF * f < 0:
            zs.append((a, m_of(a, W, P), mp.e ** (-W)))
        prevF = f
        if len(zs) >= 4:
            break
    for z in zs:
        print('zero of dm/dx near xi =', mp.nstr(z[0], 8), ' m =', mp.nstr(z[1], 8), ' contrast =', mp.nstr(z[2], 8))
    # min of F on [xi1+, 7]: confirm strict negativity there
    mp.mp.dps = 30
    a, W, P = mp.mpf(0), mp.mpf(0), mp.mpf(0); h = mp.mpf('0.01'); fmax = None
    while a < 7 - mp.mpf('1e-12'):
        W, P = step(a, W, P, h); a += h
        if a > mp.mpf('6.46'):
            f = mp.e ** W - P ** 2 / 2
            fmax = f if fmax is None else max(fmax, f)
    print('max of F on grid [6.46,7]:', mp.nstr(fmax, 10))
    W, P = state(7)
    print('m(7) =', mp.nstr(m_of(mp.mpf(7), W, P), 15), ' F(7) =', mp.nstr(mp.e ** W - P ** 2 / 2, 10))
