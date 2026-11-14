"""Method B: high-precision Taylor-series integration (mpmath) of the isothermal Emden equation.
Variables: t = log xi, z = w + 2t; z'' = 2 - z' - e^z (autonomous).
m^2 * 4pi = u v^3 with v = 2 - z', u = e^z / v. Extrema of m: 2u = v  <=>  g = 2 e^z - (2 - z')^2 = 0.
Start: power series of w in y = xi^2 at xi0 = 0.05.
"""
import mpmath as mp
import sys

mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
ORDER = int(sys.argv[2]) if len(sys.argv) > 2 else 40
H = mp.mpf(sys.argv[3]) if len(sys.argv) > 3 else mp.mpf('0.05')
TEND = mp.log(mp.mpf(sys.argv[4])) if len(sys.argv) > 4 else mp.log(2000)

# series w = sum a_k y^k, y = x^2 ; E = e^w = sum b_k y^k
# (x^2 w')' = -x^2 E.  w' = sum 2k a_k x^{2k-1}; x^2 w' = sum 2k a_k x^{2k+1}; derivative = sum 2k(2k+1) a_k x^{2k}
# so 2k(2k+1) a_k = -b_{k-1}
N = 60
a = [mp.mpf(0)] * (N + 1)
b = [mp.mpf(0)] * (N + 1)
b[0] = mp.mpf(1)
for k in range(1, N + 1):
    a[k] = -b[k - 1] / (2 * k * (2 * k + 1))
    # E' = w' E in y: k b_k = sum_{j=1..k} j a_j b_{k-j}
    b[k] = sum(j * a[j] * b[k - j] for j in range(1, k + 1)) / k
x0 = mp.mpf('0.05')
w0 = sum(a[k] * x0 ** (2 * k) for k in range(N + 1))
dw0 = sum(2 * k * a[k] * x0 ** (2 * k - 1) for k in range(1, N + 1))
t = mp.log(x0)
z = w0 + 2 * t
zp = x0 * dw0 + 2  # z_t = xi w' + 2


def taylor(z0, zp0, n):
    """Taylor coefficients c_k of z(t0+s) about s=0."""
    c = [mp.mpf(0)] * (n + 1)
    e = [mp.mpf(0)] * (n + 1)
    c[0] = z0
    c[1] = zp0
    e[0] = mp.e ** z0
    # e' = z' e : k e_k = sum_{j=1..k} j c_j e_{k-j}
    for k in range(0, n - 1):
        # need e_k: computed from c_1..c_k
        if k >= 1:
            e[k] = sum(j * c[j] * e[k - j] for j in range(1, k + 1)) / k
        # z'' = 2 - z' - e  => (k+2)(k+1) c_{k+2} = [2]_k - (k+1) c_{k+1} - e_k
        rhs = (2 if k == 0 else 0) - (k + 1) * c[k + 1] - e[k]
        c[k + 2] = rhs / ((k + 2) * (k + 1))
    return c


def ev(c, s):
    v = mp.mpf(0)
    d = mp.mpf(0)
    for k in range(len(c) - 1, -1, -1):
        d = d * s + v if False else d
    # Horner for value and derivative
    p = mp.mpf(0)
    dp = mp.mpf(0)
    for k in range(len(c) - 1, -1, -1):
        dp = dp * s + p
        p = p * s + c[k]
    return p, dp


def gfun(zz, zzp):
    return 2 * mp.e ** zz - (2 - zzp) ** 2


def mass(tt, zz, zzp):
    v = 2 - zzp
    u = mp.e ** zz / v
    return mp.sqrt(u * v ** 3 / (4 * mp.pi))


ext = []
gprev = gfun(z, zp)
while t < TEND:
    h = min(H, TEND - t)
    c = taylor(z, zp, ORDER)
    zn, zpn = ev(c, h)
    gn = gfun(zn, zpn)
    if mp.sign(gn) != mp.sign(gprev):
        f = lambda s: gfun(*ev(c, s))
        s0 = mp.findroot(f, (mp.mpf(0), h), solver='anderson')
        zs, zps = ev(c, s0)
        ts = t + s0
        xi = mp.e ** ts
        mm = mass(ts, zs, zps)
        w = zs - 2 * ts
        ext.append((xi, mm, mp.e ** (-w)))
        print('extremum xi=%s m=%s contrast=%s' % (mp.nstr(xi, 20), mp.nstr(mm, 20), mp.nstr(mp.e ** (-w), 20)))
    t, z, zp, gprev = t + h, zn, zpn, gn
xi = mp.e ** t
v = 2 - zp
u = mp.e ** z / v
V = (u - 1 - mp.log(u)) + (v - 2 - 2 * mp.log(v / 2))
print('at xi=%s: u=%s v=%s V=%s m=%s' % (mp.nstr(xi, 15), mp.nstr(u, 20), mp.nstr(v, 20), mp.nstr(V, 20), mp.nstr(mass(t, z, zp), 20)))
