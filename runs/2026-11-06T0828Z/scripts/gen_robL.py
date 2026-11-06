"""Robertson at long horizons, t in [40, 1e11]: collocation cells in mpmath, exact rational
defects, sheared weight N(e)^2 = d^2 e2^2 + (e3 + c e2)^2 per cell, one-sided bound mu <= 0 from
a corner PSD certificate (8 corners: x2, x3 box ends, h2 = +-B/d), contracting propagation
(Work.Sim.OneSidedNeg.onesided_cell_neg).  Feasibility + certificate data.
Usage: python3 gen_robL.py [DEG] [PERDEC] [D] [DIGITS] [out.json]"""
import sys, json, math
from fractions import Fraction as Fr
import mpmath as mp
import numpy as np
from scipy.integrate import solve_ivp

DEG = int(sys.argv[1]) if len(sys.argv) > 1 else 14
PERDEC = int(sys.argv[2]) if len(sys.argv) > 2 else 12
D = Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(1)
DIG = int(sys.argv[4]) if len(sys.argv) > 4 else 50
OUT = sys.argv[5] if len(sys.argv) > 5 else None
mp.mp.dps = DIG + 25
K1, K2, K3 = Fr(1, 25), Fr(10000), Fr(30000000)
k1, k2, k3 = 0.04, 1e4, 3e7
W = D * D
# t = 40 ball of Work.Sim.Robertson.chain (weight 4900 e2^2 + e3^2)
C2_40 = Fr(4592767382278885557, 500000000000000000000000)
C3_40 = Fr(2841637457458304589, 10000000000000000000)
DELTA40 = Fr(183, 100000000000)

def F(t, y):
    y2, y3 = y; y1 = 1 - y2 - y3
    return [k1*y1 - k2*y2*y3 - k3*y2*y2, k3*y2*y2]
def Jac(t, y):
    y2, y3 = y
    return [[-k1 - k2*y3 - 2*k3*y2, -k1 - k2*y2], [2*k3*y2, 0.0]]
ref = solve_ivp(F, (40, 1e11), [float(C2_40), float(C3_40)], method='LSODA', jac=Jac,
                rtol=1e-11, atol=1e-21, dense_output=True)
assert ref.success

def sig(x, n=3, up=True):
    x = Fr(x)
    if x == 0: return Fr(0)
    if x < 0: return -sig(-x, n, not up)
    e = math.floor(math.log10(float(x))) - n + 1
    q = Fr(10)**e
    return (Fr(math.ceil(x / q)) if up else Fr(math.floor(x / q))) * q

def grid():
    ts = []
    for dec in range(9):           # 40*10^dec .. 40*10^(dec+1)
        for j in range(PERDEC):
            ts.append(sig(Fr(40) * Fr(10)**dec * Fr(10**(j / PERDEC)).limit_denominator(10**6), 3))
    ts.append(Fr(4 * 10**10))
    for j in range(1, 5):
        ts.append(sig(Fr(4 * 10**10) * Fr(2.5 ** (j / 5)).limit_denominator(10**6), 3))
    ts.append(Fr(10**11))
    out = []
    for t in ts:
        if not out or t > out[-1]: out.append(t)
    return out

# polynomials: lists of Fractions, low order first, variable u = t - mid
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pscale(a, c): return [c*x for x in a]
def pmul(a, b):
    r = [Fr(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b): r[i+j] += x*y
    return r
def pder(a): return [i*a[i] for i in range(1, len(a))] or [Fr(0)]
def peval(a, x):
    r = Fr(0)
    for c in reversed(a): r = r*x + c
    return r
from math import comb
def cheb(a, h):
    """Exact Chebyshev coefficients of s -> a(h s) on [-1, 1]: a(h s) = sum b_j T_j(s)."""
    n = len(a); b = [Fr(0)] * n
    for k, c in enumerate(a):
        if c == 0: continue
        ck = c * h**k
        # s^k = 2^(1-k) sum_{j<=k/2} binom(k,j) T_{k-2j}, with the T_0 term halved
        for j in range(k // 2 + 1):
            m = k - 2*j
            coef = Fr(comb(k, j), 2**(k - 1)) if k > 0 else Fr(1)
            if m == 0 and k > 0: coef /= 2
            b[m] += ck * coef
    return b
def absbound(a, h): return sum(abs(c) for c in cheb(a, h))
def lowup(a, h):
    b = cheb(a, h)
    rest = sum(abs(c) for c in b[1:])
    return b[0] - rest, b[0] + rest

def fit(t0, h, c0, n):
    """Collocation in s in [-1, 1] (u = r s): p(-1) = c0, ODE at n Chebyshev points; Newton in mp."""
    r = mp.mpf(h.numerator) / h.denominator / 2
    mid = float(t0 + h / 2)
    sj = [-mp.cos(mp.pi * (j + mp.mpf(1) / 2) / n) for j in range(n)]
    m = 3 * n
    sl = -np.cos(np.pi * (np.arange(m) + 0.5) / m)
    Y = ref.sol(mid + sl * float(r))
    V = np.vstack([sl**k for k in range(n + 1)]).T
    a = [mp.mpf(x) for c in range(2) for x in np.linalg.lstsq(V, Y[c], rcond=None)[0]]
    N = n + 1
    c0m = [mp.mpf(c0[0].numerator) / c0[0].denominator, mp.mpf(c0[1].numerator) / c0[1].denominator]
    a[0] += c0m[0] - sum(a[k] * (-1)**k for k in range(N))
    a[N] += c0m[1] - sum(a[N + k] * (-1)**k for k in range(N))
    Pm = [[s**k for k in range(N)] for s in sj]
    dPm = [[(k * s**(k - 1) if k > 0 else mp.mpf(0)) / r for k in range(N)] for s in sj]
    K1m, K2m, K3m = mp.mpf(1) / 25, mp.mpf(10000), mp.mpf(30000000)
    # y2: ODE at n+1 Chebyshev points (no initial condition: p2 sits on the slow manifold; the
    # start mismatch is charged to delta); y3: initial condition + ODE at n points.
    sk = [-mp.cos(mp.pi * (j + mp.mpf(1) / 2) / N) for j in range(N)]
    Pk = [[s**k for k in range(N)] for s in sk]
    dPk = [[(k * s**(k - 1) if k > 0 else mp.mpf(0)) / r for k in range(N)] for s in sk]
    for it in range(40):
        a2, a3 = a[:N], a[N:]
        y2k = [mp.fsum(Pk[j][k] * a2[k] for k in range(N)) for j in range(N)]
        y3k = [mp.fsum(Pk[j][k] * a3[k] for k in range(N)) for j in range(N)]
        y2 = [mp.fsum(Pm[j][k] * a2[k] for k in range(N)) for j in range(n)]
        y3 = [mp.fsum(Pm[j][k] * a3[k] for k in range(N)) for j in range(n)]
        res = [mp.fsum(dPk[j][k] * a2[k] for k in range(N)) - (K1m*(1 - y2k[j] - y3k[j]) - K2m*y2k[j]*y3k[j] - K3m*y2k[j]**2) for j in range(N)]
        res += [mp.fsum(a3[k] * (-1)**k for k in range(N)) - c0m[1]]
        res += [mp.fsum(dPm[j][k] * a3[k] for k in range(N)) - K3m*y2[j]**2 for j in range(n)]
        Jm = mp.matrix(2 * N, 2 * N)
        for k in range(N):
            Jm[N, N + k] = (-1)**k
        for j in range(N):
            for k in range(N):
                Jm[j, k] = dPk[j][k] - (-K1m - K2m*y3k[j] - 2*K3m*y2k[j]) * Pk[j][k]
                Jm[j, N + k] = -(-K1m - K2m*y2k[j]) * Pk[j][k]
        for j in range(n):
            for k in range(N):
                Jm[N + 1 + j, k] = -(2*K3m*y2[j]) * Pm[j][k]
                Jm[N + 1 + j, N + k] = dPm[j][k]
        da = mp.lu_solve(Jm, -mp.matrix(res))
        a = [a[i] + da[i] for i in range(2 * N)]
        if max(abs(x) for x in da) < mp.mpf(10)**(-(DIG + 15)): break
    rr = Fr(h, 2)
    out = []
    scale = Fr(10)**DIG
    for comp in range(2):
        coef = a[comp*N:(comp+1)*N]
        out.append([Fr(int(mp.nint(c * 10**DIG))) / scale / rr**k for k, c in enumerate(coef)])
    return out

def corner_mu(d, c, L2, U2, L3, U3, B):
    w = d * d; hb = B / d
    best = None
    for x2 in (L2, U2):
        for x3 in (L3, U3):
            for h2 in (-hb, hb):
                al = (c*K1 + c*K2*x2 - K1 - K2*x3 - 2*K3*x2) + h2*(c*K2 - K3)
                be = (c*c*K1 + c*c*K2*x2 - c*K1 - c*K2*x3 - 2*c*K3*x2 - K1*w - K2*w*x2 + 2*K3*x2) / d \
                     + h2*(c*c*K2 - c*K3 - K2*w + K3) / d
                ga = -c*(K1 + K2*x2) + h2*(-c*K2)
                af, gf, bf = mp.mpf(al.numerator)/al.denominator, mp.mpf(ga.numerator)/ga.denominator, mp.mpf(be.numerator)/be.denominator
                m = ((af + gf) + mp.sqrt((af - gf)**2 + bf**2)) / 2
                best = m if best is None or m > best else best
    return best

def corner_ok(d, c, L2, U2, L3, U3, B, mu):
    w = d * d; hb = B / d
    for x2 in (L2, U2):
        for x3 in (L3, U3):
            for h2 in (-hb, hb):
                al = (c*K1 + c*K2*x2 - K1 - K2*x3 - 2*K3*x2) + h2*(c*K2 - K3)
                be = (c*c*K1 + c*c*K2*x2 - c*K1 - c*K2*x3 - 2*c*K3*x2 - K1*w - K2*w*x2 + 2*K3*x2) / d \
                     + h2*(c*c*K2 - c*K3 - K2*w + K3) / d
                ga = -c*(K1 + K2*x2) + h2*(-c*K2)
                if not (mu - al > 0 and 4*(mu - al)*(mu - ga) >= be*be): return False
    return True

def best_c(d, L2, U2, L3, U3, B, x2m, x3m):
    # analytic guess: QL of the left-eigenvector matrix (fast row scaled by d)
    J11 = -k1 - k2*x3m - 2*k3*x2m; J12 = -k1 - k2*x2m; J21 = 2*k3*x2m
    tr = J11; det = -J12*J21
    lf = (tr - math.sqrt(tr*tr - 4*det)) / 2
    b = J12 / lf                      # fast left eigenvector (1, b)
    s = float(d); th = math.atan(b * s)
    cs = -J21 / (J11 - (tr - lf))     # slow left eigenvector (cs, 1): cs*J11 + J21 = ls*cs
    cg = (s * math.sin(th) + cs * math.cos(th)) / (math.cos(th) - 0 * math.sin(th))
    f = lambda cc: float(corner_mu(d, Fr(cc).limit_denominator(10**40), L2, U2, L3, U3, B))
    lo, hi = cg * 0.5, cg * 1.5
    if cg == 0: lo, hi = -1e-6, 1e-6
    g = (math.sqrt(5) - 1) / 2
    a, bq = lo, hi
    x1, x2 = bq - g*(bq - a), a + g*(bq - a); f1, f2 = f(x1), f(x2)
    for _ in range(80):
        if f1 < f2: bq, x2, f2 = x2, x1, f1; x1 = bq - g*(bq - a); f1 = f(x1)
        else: a, x1, f1 = x1, x2, f2; x2 = a + g*(bq - a); f2 = f(x2)
    return sig(Fr((a + bq) / 2), 12), cg

def run():
    ts = grid()
    d = D
    cells = []
    cc = [C2_40, C3_40]
    # 4900 e2^2 + e3^2 <= DELTA40^2 => |e2| <= DELTA40/70, |e3| <= DELTA40
    e2b, e3b = DELTA40 / 70, DELTA40
    cprev = None
    Delta = None
    for i in range(len(ts) - 1):
        t0, t1 = ts[i], ts[i + 1]; h = t1 - t0; r = h / 2
        p2, p3 = fit(t0, h, cc, DEG)
        f2 = padd(padd(pscale(padd([Fr(1)], pscale(padd(p2, p3), -1)), K1), pscale(pmul(p2, p3), -K2)), pscale(pmul(p2, p2), -K3))
        f3 = pscale(pmul(p2, p2), K3)
        d2 = padd(pder(p2), pscale(f2, -1)); d3 = padd(pder(p3), pscale(f3, -1))
        e2 = sig(absbound(d2, r)); e3 = sig(absbound(d3, r))
        L2, U2 = lowup(p2, r); L3, U3 = lowup(p3, r)
        x2m, x3m = float(p2[0]), float(p3[0])
        # radius guess for c optimisation
        Bg = Fr(1, 10**12) if Delta is None else max(Delta * 2, Fr(1, 10**40))
        c, cg = best_c(d, L2, U2, L3, U3, Bg, x2m, x3m)
        eps = sig(Fr(math.sqrt(float(W*e2*e2 + (e3 + abs(c)*e2)**2))) * Fr(1001, 1000) + Fr(1, 10**60))
        assert W*e2*e2 + (e3 + abs(c)*e2)**2 < eps*eps
        if Delta is None:
            Dst = sig(d * e2b + e3b + abs(c) * e2b)      # sheared norm of the t = 40 ball
        else:
            Dst = sig(Delta * (1 + abs(c - cprev) / d))    # weight change
        st2, st3 = peval(p2, -r), peval(p3, -r)
        m2, m3 = cc[0] - st2, cc[1] - st3
        delta = sig(Dst + d * abs(m2) + abs(m3 + c * m2) + Fr(1, 10**60))
        B = sig(delta + eps * h)
        mu = None
        for _ in range(30):
            mf = corner_mu(d, c, L2, U2, L3, U3, B)
            mu = sig(Fr(mp.nstr(mf * (1 - mp.mpf(10)**-3) if mf < 0 else mf * (1 + mp.mpf(10)**-3) + mp.mpf(10)**-60, 30)), 3)
            k = 0
            while not corner_ok(d, c, L2, U2, L3, U3, B, mu):
                mu = sig(mu * Fr(999, 1000) if mu < 0 else mu * Fr(1001, 1000) + Fr(1, 10**40), 4); k += 1
                assert k < 200
            Bn = sig(delta + eps * h) if mu <= 0 else sig((delta + eps*h) * (1 + mu*h + (mu*h)**2))
            if Bn <= B: break
            B = Bn
        if mu > 0:
            print('FAIL', i, float(t0), float(h), 'mu', float(mu), 'B', float(B), 'delta', float(delta), 'eps', float(eps), 'Dst', float(Dst),
                  'mu(B tiny)', mp.nstr(corner_mu(d, c, L2, U2, L3, U3, Fr(1, 10**50)), 5), 'c', float(c), 'x2', float(L2), float(U2), 'x3', float(L3), float(U3), flush=True)
        assert mu <= 0, (i, float(t0), float(mu))
        assert -Fr(1, 1000) <= L2 - B/d and U2 + B/d <= Fr(1, 1000) and Fr(-1, 10) <= L3 - B and U3 + B <= Fr(11, 10)
        endR = delta / (1 - mu * h) + eps * h
        E2, E3 = peval(p2, r), peval(p3, r)
        n2 = Fr(round(E2 * 10**(DIG + 5)), 10**(DIG + 5)); n3 = Fr(round(E3 * 10**(DIG + 5)), 10**(DIG + 5))
        Dn = sig(endR + d * abs(E2 - n2) + abs(E3 - n3 + c * (E2 - n2)) + Fr(1, 10**60))
        cells.append(dict(t0=t0, h=h, p2=p2, p3=p3, d2=d2, d3=d3, e2=e2, e3=e3, eps=eps, c=c, mu=mu,
                          L2=L2, U2=U2, L3=L3, U3=U3, Dst=Dst, delta=delta, B=B, c2=cc[0], c3=cc[1],
                          n2=n2, n3=n3, Dn=Dn))
        cl = cells[-1]
        print(f"{i:3d} t0={float(cl['t0']):.4g} h={float(cl['h']):.3g} e2={float(cl['e2']):.1e} e3={float(cl['e3']):.1e} eps={float(cl['eps']):.2e} "
              f"c={float(cl['c']):.4e} mu={float(cl['mu']):.3e} (-2/t {-2/float(cl['t0']+cl['h']):.2e}) delta={float(cl['delta']):.2e} B={float(B):.2e} Dn={float(cl['Dn']):.3e} y2={float(cl['n2']):.6e}", flush=True)
        Delta, cprev, cc = Dn, c, [n2, n3]
    return cells

if __name__ == '__main__':
    cells = run()
    for i, cl in enumerate([]):
        print(f"{i:3d} t0={float(cl['t0']):.4g} h={float(cl['h']):.3g} e2={float(cl['e2']):.1e} e3={float(cl['e3']):.1e} eps={float(cl['eps']):.2e} "
              f"c={float(cl['c']):.4e} mu={float(cl['mu']):.3e} (-2/t {-2/float(cl['t0']+cl['h']):.2e}) delta={float(cl['delta']):.2e} Dn={float(cl['Dn']):.3e} y2={float(cl['n2']):.6e}", flush=True)
    last = cells[-1]
    Dl, c = last['Dn'], last['c']
    print('cells', len(cells), 'final N radius', float(Dl), ' |e2| <=', float(Dl / D), ' |e3| <=', float(Dl + abs(c) * Dl / D))
    print('y1 =', float(1 - last['n2'] - last['n3']), 'y2 =', float(last['n2']), 'y3 =', float(last['n3']))
    if OUT:
        json.dump([{k: str(v) if not isinstance(v, list) else [str(x) for x in v] for k, v in cl.items()} for cl in cells], open(OUT, 'w'))
