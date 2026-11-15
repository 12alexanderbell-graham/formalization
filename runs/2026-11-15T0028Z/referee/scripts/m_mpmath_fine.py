"""Method A: own fixed-step Taylor-series integrator in mpmath (30 digits) for the homology system
du/dt = u(3-u-v), dv/dt = v(u-1), t = log xi; started from the power series of w at small xi
(with an independent Taylor-series start in xi to avoid relying on a hand-typed series).
Zeros of 2u - v located by Newton on the local Taylor polynomial. mass = sqrt(u v^3 / (4 pi))."""
import mpmath as mp
mp.mp.dps = 40

# --- power series of w around xi = 0 by recursion: (x^2 w')' = -x^2 e^w, w even.
def w_series(nterms):
    # w = sum a_k x^(2k), E = e^w = sum b_k x^(2k)
    a = [mp.mpf(0)]*nterms; b = [mp.mpf(0)]*nterms
    b[0] = mp.mpf(1)
    for k in range(1, nterms):
        # (x^2 w')' = sum a_k 2k(2k+1) x^(2k)  = - sum b_{k-1} x^(2k)
        a[k] = -b[k-1]/(2*k*(2*k+1))
        # E' = w' E  ->  2k b_k = sum_{j=1..k} 2j a_j b_{k-j}
        b[k] = sum(2*j*a[j]*b[k-j] for j in range(1, k+1))/(2*k)
    return a

A = w_series(40)
print("series coeffs:", [mp.nstr(c, 12) for c in A[:5]])
x0 = mp.mpf('0.05')
w0 = sum(A[k]*x0**(2*k) for k in range(40))
p0 = sum(2*k*A[k]*x0**(2*k-1) for k in range(1, 40))
u = x0*mp.e**w0/(-p0); v = -x0*p0
t = mp.log(x0)

ORDER = 40
def taylor(u, v, n=ORDER):
    U = [u]+[mp.mpf(0)]*n; V = [v]+[mp.mpf(0)]*n
    for k in range(n):
        # (UV)_k, (UU)_k
        uu = sum(U[j]*U[k-j] for j in range(k+1))
        uv = sum(U[j]*V[k-j] for j in range(k+1))
        U[k+1] = (3*U[k] - uu - uv)/(k+1)
        V[k+1] = (uv - V[k])/(k+1)
    return U, V

def peval(C, h):
    s = mp.mpf(0)
    for c in reversed(C): s = s*h + c
    return s
def pder(C, h):
    s = mp.mpf(0)
    for k in range(len(C)-1, 0, -1): s = s*h + k*C[k]
    return s

H = mp.mpf('0.02')
T1 = mp.log(mp.mpf('2e8'))
T300k = mp.log(mp.mpf(300000))
res = []
while t < T1:
    U, V = taylor(u, v)
    h = H
    if t < T300k < t + h:
        hh = T300k - t
        uu, vv = peval(U, hh), peval(V, hh)
        e1, e2 = uu-1, vv-2
        N300 = 7*e1**2 + (e1+2*e2)**2
        print("N(300000) =", mp.nstr(N300, 20), " sqrtN =", mp.nstr(mp.sqrt(N300), 20),
              " u,v =", mp.nstr(uu, 20), mp.nstr(vv, 20))
    G = [2*U[k]-V[k] for k in range(len(U))]
    g0, g1 = peval(G, 0), peval(G, h)
    if g0*g1 < 0 or g1 == 0:
        s = h/2
        for _ in range(60):
            s = s - peval(G, s)/pder(G, s)
        uu, vv = peval(U, s), peval(V, s)
        te = t + s
        res.append((te, uu, vv))
    u, v = peval(U, h), peval(V, h)
    t += h

sq = mp.sqrt(2/mp.pi)
print("sqrt(2/pi) =", mp.nstr(sq, 25))
for i, (te, uu, vv) in enumerate(res):
    m = mp.sqrt(uu*vv**3/(4*mp.pi))
    print(i, "xi =", mp.nstr(mp.e**te, 22), " m =", mp.nstr(m, 22), " u =", mp.nstr(uu, 18),
          " m/(u^2 sqrt(2/pi)) =", mp.nstr(m/(uu**2*sq), 12),
          " d(2u-v)/dt / (8u(1-u)) =", mp.nstr((2*uu*(3-uu-vv) - vv*(uu-1))/(8*uu*(1-uu)), 12))
