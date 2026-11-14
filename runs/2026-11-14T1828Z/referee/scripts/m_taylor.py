# Method B: arbitrary-precision Taylor-series integrator (mpmath) for
#   z' = y + 2, y' = -y - e^z   (t = log xi, z = w + 2t, y = xi w')
# started from the power series of w at xi = 0 (independent of method A's start).
import sys
from mpmath import mp, mpf, exp, log, sqrt, pi, findroot
mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
H = mpf(sys.argv[2]) if len(sys.argv) > 2 else mpf('0.05')
N = 30

def w_series(xi, K=80):
    a = [mpf(0)]*(K+1); b = [mpf(0)]*(K+1); b[0] = mpf(1)
    for k in range(1, K+1):
        a[k] = -b[k-1]/(2*k*(2*k+1))
        b[k] = sum(j*a[j]*b[k-j] for j in range(1, k+1))/k
    x = xi*xi
    w = sum(a[k]*x**k for k in range(K+1))
    dw = sum(2*k*a[k]*xi**(2*k-1) for k in range(1, K+1))
    return w, dw

def coeffs(z0, y0):
    z = [z0]; y = [y0]; E = [exp(z0)]
    for k in range(N):
        z.append((y[k] + (2 if k == 0 else 0))/(k+1))
        y.append((-y[k] - E[k])/(k+1))
        kk = k+1
        E.append(sum(j*z[j]*E[kk-j] for j in range(1, kk+1))/kk)
    return z, y

def ev(c, h):
    s = mpf(0)
    for a in reversed(c): s = s*h + a
    return s

def F(z, y):  # extremum indicator  y^2 - 2 e^z  (sign change at extrema of m)
    return y*y - 2*exp(z)

def m_of(z, y): return -y*exp(z/2)/sqrt(4*pi)

xi0 = mpf('0.5')
w0, dw0 = w_series(xi0)
t = log(xi0); z = w0 + 2*t; y = xi0*dw0
T1 = log(mpf(10)**7)
T3 = log(mpf(300000))
ext = []
Vt3 = None
maxm_after = {}  # running max of m on grid for xi >= xi4 (excluding near xi5)
grid_ms = []
while t < T1:
    h = min(H, T1 - t)
    zc, yc = coeffs(z, y)
    if Vt3 is None and t + h >= T3:
        hh = T3 - t
        z3, y3 = ev(zc, hh), ev(yc, hh)
        v = -y3; u = exp(z3)/v
        Vt3 = (u - 1 - log(u)) + (v - 2 - 2*log(v/2)), u, v
    f0 = F(z, y)
    z1, y1 = ev(zc, h), ev(yc, h)
    f1 = F(z1, y1)
    if f0*f1 < 0:
        g = lambda s: F(ev(zc, s), ev(yc, s))
        s = findroot(g, (mpf(0), h), solver='anderson')
        ze, ye = ev(zc, s), ev(yc, s)
        ext.append((t + s, ze, ye))
    # sample m on sub-grid for the sup check
    for i in range(1, 6):
        s = h*i/5
        grid_ms.append((t + s, m_of(ev(zc, s), ev(yc, s))))
    t, z, y = t + h, z1, y1

for te, ze, ye in ext:
    xi = exp(te); w = ze - 2*te
    print("xi=", mp.nstr(xi, 20), " m=", mp.nstr(m_of(ze, ye), 20), " contrast=", mp.nstr(exp(-w), 20))
print("m(1e7)=", mp.nstr(m_of(z, y), 20))
print("V(3e5)=", mp.nstr(Vt3[0], 15), " u=", mp.nstr(Vt3[1], 15), " v=", mp.nstr(Vt3[2], 15))
xi4 = exp(ext[3][0]); xi5 = exp(ext[4][0]); m5 = m_of(ext[4][1], ext[4][2])
far = [m for (tt, m) in grid_ms if exp(tt) >= xi4 and abs(exp(tt) - xi5) >= 1]
print("grid sup m over xi>=xi4, |xi-xi5|>=1 (grid only):", mp.nstr(max(far), 20))
# exact sup on |xi-xi5|>=1 is attained at xi5 +- 1 (m unimodal near xi5): evaluate there via local Taylor
for sgn in (-1, 1):
    target = log(xi5 + sgn)
    # step from the extremum point
    tt, zz, yy = ext[4]
    zc, yc = coeffs(zz, yy); d = target - tt
    print(f"m(xi5{'+' if sgn > 0 else '-'}1)=", mp.nstr(m_of(ev(zc, d), ev(yc, d)), 20),
          " m5 - that =", mp.nstr(m5 - m_of(ev(zc, d), ev(yc, d)), 6))
# max of u v^3 on {V <= V0}: Lagrange gives v = 3u - 1 (u > 1 branch)
V0 = Vt3[0]
G = lambda u: (u - 1 - log(u)) + (3*u - 3 - 2*log((3*u - 1)/2)) - V0
ustar = findroot(G, mpf(1) + sqrt(V0/ 6))
vstar = 3*ustar - 1
print("argmax u*, v* =", mp.nstr(ustar, 15), mp.nstr(vstar, 15), " max u v^3 =", mp.nstr(ustar*vstar**3, 20))
print("4 pi m5^2 =", mp.nstr(4*pi*m5**2, 20), " 8 =", 8)
print("max-mass bound beyond 3e5: sqrt(max uv^3/4pi)=", mp.nstr(sqrt(ustar*vstar**3/(4*pi)), 20))
