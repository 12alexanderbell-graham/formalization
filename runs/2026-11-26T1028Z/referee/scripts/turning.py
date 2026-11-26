# Independent computation of Gelfand turning points (3-ball, radial), Taylor-series integrator in mpmath.
import mpmath as mp, sys
def run(dps, h, order):
    mp.mp.dps = dps
    # power series of w at 0: w = sum a_n s^n
    N = 160
    a = [mp.mpf(0)]*(N+3); e = [mp.mpf(0)]*(N+3); e[0] = mp.mpf(1)
    for n in range(0, N+1):
        if n >= 1:
            e[n] = sum(k*a[k]*e[n-k] for k in range(1, n+1))/n
        a[n+2] = -e[n]/((n+2)*(n+3))
    s0 = mp.mpf('0.25')
    w = sum(a[n]*s0**n for n in range(N+3))
    wp = sum(n*a[n]*s0**(n-1) for n in range(1, N+3))
    u = s0*mp.e**w/(-wp); v = -s0*wp; t = mp.log(s0)
    # Taylor integrate du/dt=u(3-u-v), dv/dt=v(u-1)
    zetas = []; lams = []
    def coeffs(u0, v0):
        U = [u0]; V = [v0]
        for n in range(order):
            uu = sum(U[k]*U[n-k] for k in range(n+1)); uv = sum(U[k]*V[n-k] for k in range(n+1))
            U.append((3*U[n] - uu - uv)/(n+1)); V.append((uv - V[n])/(n+1))
        return U, V
    def ev(C, x): 
        r = mp.mpf(0)
        for c in reversed(C): r = r*x + c
        return r
    def dev(C, x):
        r = mp.mpf(0)
        for i in range(len(C)-1, 0, -1): r = r*x + i*C[i]
        return r
    tend = mp.log(mp.mpf('1e17'))
    while t < tend and len(zetas) < 16:
        U, V = coeffs(u, v)
        v1 = ev(V, h)
        if (v - 2)*(v1 - 2) < 0:
            x = h/2
            for _ in range(100):
                dx = (ev(V, x) - 2)/dev(V, x); x -= dx
                if abs(dx) < mp.mpf(10)**(-dps+5): break
            zetas.append(mp.e**(t + x)); lams.append(ev(U, x)*ev(V, x))
        u, v = ev(U, h), v1; t += h
    return zetas, lams

A = run(40, mp.mpf('0.05'), 30)
B = run(50, mp.mpf('0.025'), 40)
mp.mp.dps = 40
L1 = mp.e**(2*mp.pi/mp.sqrt(7)); L2 = -mp.e**(-mp.pi/mp.sqrt(7))
print("limits", mp.nstr(L1, 20), mp.nstr(L2, 20))
for k,(z,l) in enumerate(zip(*A)):
    zb, lb = B[0][k], B[1][k]
    print(k, mp.nstr(z, 20), mp.nstr(l, 20), " relerr zeta %.1e lam %.1e" % (float(abs(z-zb)/zb), float(abs(l-lb))))
zs, ls = B
for n in range(0, len(zs)-7):
    r = zs[n+7]/zs[n+6]; d = (ls[n+7]-2)/(ls[n+6]-2)
    d1 = abs(r - L1); d2 = abs(d - L2)
    b1 = mp.mpf(47)/100*(mp.mpf(33)/100)**n; b2 = mp.mpf(3)/100*(mp.mpf(33)/100)**n
    print("n=%d ratio=%s dist1=%.6e /b1=%.4f  devq=%s dist2=%.6e /b2=%.4f" % (n, mp.nstr(r,15), float(d1), float(d1/b1), mp.nstr(d,15), float(d2), float(d2/b2)))
for k in range(6, len(zs)):
    x = ls[k]/2 - 1  # at turning point lambda-2=2x, Nw=8x^2
    print("eps_%d = sqrt(Nw) = %.6e" % (k, float(mp.sqrt(8)*abs((ls[k]-2)/2))))
