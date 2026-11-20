# High-precision reference for the Lane-Emden equation of index 9/2 (floating point, not evidence):
# series at the centre, then mpmath's Taylor ODE solver, then the first zero by Newton on theta.
import mpmath as mp
mp.mp.dps = 40
n = mp.mpf(9)/2
# series theta = sum a_k xi^(2k): use mpmath odefun from xi0 small with series start
def series(xi, K=12):
    # coefficients by recursion for theta = sum c_k x^k (even), using power-series of theta^n
    N = 2*K+2
    c = [mp.mpf(0)]*(N+1); c[0] = mp.mpf(1)
    # theta'' + 2/x theta' = -theta^n ; for x^k term: c_{k+2}(k+2)(k+3) = -[theta^n]_k
    for k in range(0, N-1):
        # compute [theta^n]_k with known c[0..k]
        # power series of f = theta^n: f0 = 1, f_m = 1/(m c0) sum_{j=1}^m (n j - m + j) c_j f_{m-j}
        f = [mp.mpf(1)]
        for m in range(1, k+1):
            s = mp.mpf(0)
            for j in range(1, m+1):
                s += (n*j - m + j) * c[j] * f[m-j]
            f.append(s/m)
        c[k+2] = -f[k]/((k+2)*(k+3))
    th = sum(c[k]*xi**k for k in range(N+1))
    ph = sum(k*c[k]*xi**(k-1) for k in range(1, N+1))
    return th, ph
x0 = mp.mpf('0.1')
t0, p0 = series(x0)
f = mp.odefun(lambda x, y: [y[1], -2*y[1]/x - (y[0] if y[0] > 0 else 0)**n], x0, [t0, p0], tol=mp.mpf(10)**-35, degree=30)
z = mp.findroot(lambda x: f(x)[0], mp.mpf('31.836'))
th, ph = f(z)
om = -z**2*ph
print('xi1', mp.nstr(z, 25))
print('omega', mp.nstr(om, 25))
print('conc', mp.nstr(z**3/(3*om), 25))
print('theta(32)', mp.nstr(f(mp.mpf('32'))[0], 10))
