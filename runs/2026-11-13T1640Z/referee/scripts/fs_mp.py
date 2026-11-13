import sys
from mpmath import mp, mpf, pcfd, findroot, nstr

mp.dps = 40

def step(y, beta, h, N):
    # Taylor coefficients of f about current point
    a = [mpf(0)] * (N + 4)
    a[0], a[1], a[2] = y[0], y[1], y[2] / 2
    for k in range(N):
        # coefficient of t^k in f f'' and f'^2
        ffpp = mpf(0); fp2 = mpf(0)
        for j in range(k + 1):
            ffpp += a[j] * (k - j + 1) * (k - j + 2) * a[k - j + 2]
            fp2 += (j + 1) * a[j + 1] * (k - j + 1) * a[k - j + 1]
        rhs = -ffpp - beta * ((1 if k == 0 else 0) - fp2)
        a[k + 3] = rhs / ((k + 1) * (k + 2) * (k + 3))
    f = sum(a[k] * h**k for k in range(N + 3))
    fp = sum(k * a[k] * h**(k - 1) for k in range(1, N + 3))
    fpp = sum(k * (k - 1) * a[k] * h**(k - 2) for k in range(2, N + 3))
    return [f, fp, fpp]

def integrate(s, beta, L, h, N, track=False):
    y = [mpf(0), mpf(0), mpf(s)]
    n = int(round(L / h))
    minq = y[2]; maxp = y[1]
    traj = []
    for i in range(n):
        y = step(y, beta, mpf(h), N)
        minq = min(minq, y[2]); maxp = max(maxp, y[1])
        if track: traj.append(((i + 1) * h, y))
    return y, minq, maxp, traj

def resid(s, beta, L, h, N):
    y, *_ = integrate(s, beta, L, h, N)
    nu = -1 - 2 * beta
    xi = y[0]
    R = pcfd(nu + 1, xi) / pcfd(nu, xi)
    return y[2] - R * (1 - y[1])

def solve(beta, L, h, N, s0):
    return findroot(lambda s: resid(s, beta, L, h, N), (mpf(s0), mpf(s0) + mpf('1e-6')), solver='secant', tol=mpf(10)**(-36))

if __name__ == '__main__':
    betas = [mpf(-13) / 100, mpf(-14) / 100, mpf(-16) / 100]
    guesses = [0.2614227559, 0.2397359553, 0.1907798552]
    for beta, g in zip(betas, guesses):
        for (L, h, N) in [(10, 0.125, 40), (12, 0.2, 30), (14, 0.125, 40), (16, 0.2, 30)]:
            s = solve(beta, L, h, N, g)
            print(nstr(beta, 4), L, h, N, nstr(s, 28), flush=True)
