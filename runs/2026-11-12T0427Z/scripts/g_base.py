"""Certificate generator for the Gelfand 3-D ball enclosure (run 2026-11-06T1228Z).

Isothermal equation w'' + (2/s) w' + e^w = 0, w(0) = 0.  Exact rational arithmetic only.
Start on [0, S0] (Work.Math.GStart.start): reference P (truncated even series of w),
residual W + s^2 T4(P) = s^2 rho with W = (s^2 P')', T4(x) = 1 + x + x^2/2 + x^3/6, and
|exp x - T4(x)| <= |x|^4 5/96, so R = sup|rho| + Mp^4 5/96.
Cells [t0, t0 + h] in the variables E = e^w, phi = w' (Work.Math.GCell.cell):
E' = E phi, phi' = -(2/t) phi - E.  Taylor polynomials through the rounded state,
coefficients rounded to 1/DEN.  Defects D1 = pe' - pe pp, D2 = (t0+s) pp' + 2 pp + (t0+s) pe.
Lipschitz K = max(1, PH + EH, 2/t0 + 1); Groenwall B = delta E + eps/K (E - 1), E = 1/(1 - K h).
Grid: from S0 with K h <= KH up to C_DEC, then up to A, then [A, B].
"""
from fractions import Fraction as F
import math, sys

N = 10
DEN = 10 ** 20
SDEN = 10 ** 20
M = F(1, 100)
S0 = F(1, 32)
X = F(41, 10)
KSER = 5          # P = sum_{k <= KSER} a_k s^(2k)
PDEN = 10 ** 26
KH = F(1, 6)
A = F(4071496844, 10 ** 9)
B = F(4071496845, 10 ** 9)
C_DEC = F(3, 1)    # switch from positivity cells to decrease cells (set by run)


def rnd(q, d):
    return F(round(q * d), d)


def ceil_q(q, d=10 ** 26):
    return F(math.ceil(q * d), d)


def ev(p, s):
    r = F(0)
    for c in reversed(p):
        r = c + s * r
    return r


def deriv(p):
    return [k * p[k] for k in range(1, len(p))] or [F(0)]


def add(*ps):
    n = max(len(p) for p in ps)
    return [sum((p[i] if i < len(p) else 0) for p in ps) for i in range(n)]


def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def sc(a, p):
    return [a * c for c in p]


def absb(p, s):
    return sum(abs(c) * s ** k for k, c in enumerate(p))


def lowb(p, s):
    return p[0] - sum(abs(c) * s ** k for k, c in enumerate(p) if k >= 1)


def upb(p, s):
    return p[0] + sum(abs(c) * s ** k for k, c in enumerate(p) if k >= 1)


def series(K):
    """w = sum a_k u^k, E = e^w = sum e_k u^k (u = s^2): a_k = -e_{k-1}/(2k(2k+1)),
    (k+1) e_{k+1} = sum_{i=0..k} e_i (k-i+1) a_{k-i+1}."""
    a = [F(0)]
    e = [F(1)]
    for k in range(1, K + 1):
        a.append(-e[k - 1] / (2 * k * (2 * k + 1)))
        # e_k from a_1..a_k, e_0..e_{k-1}
        e.append(sum(e[i] * (k - i) * a[k - i] for i in range(k)) / k)
    return a


def T4(p):
    p2 = mul(p, p)
    p3 = mul(p2, p)
    return add([F(1)], p, sc(F(1, 2), p2), sc(F(1, 6), p3))


def T6v(x):
    return 1 + x + x ** 2 / 2 + x ** 3 / 6 + x ** 4 / 24 + x ** 5 / 120


def start():
    a = series(KSER)
    P = [F(0)] * (2 * KSER + 1)
    for k, ak in enumerate(a):
        P[2 * k] = rnd(ak, PDEN)
    Pd = deriv(P)
    x2 = [F(0), F(0), F(1)]
    W = deriv(mul(x2, Pd))
    r = add(W, mul(x2, T4(P)))
    assert r[0] == 0 and r[1] == 0
    rho = r[2:]
    Mp = ceil_q(absb(P, S0), 10 ** 12)
    Rr = ceil_q(absb(rho, S0))
    R = ceil_q(Rr + Mp ** 4 * F(5, 96))
    return P, Pd, W, rho, R, Mp, Rr


def startbox(P, Pd, W, rho, R, Mp, Rr=None):
    L = F(2)                     # exp(Mp + eta) <= 2 (exp_le_two: Mp + eta <= 1/2)
    alpha = S0 ** 2 / 6 * L
    eta = ceil_q(2 * (S0 ** 2 / 6 * R) / (1 - alpha), 10 ** 40)
    eta = max(eta, F(1, 10 ** 38))
    C = L * eta + R
    assert S0 ** 2 / 6 * C < eta and Mp + eta <= F(1, 2)
    etaw = S0 ** 2 / 6 * C              # |w - P| on [0, S0]
    dphi = S0 / 3 * C                   # |phi - P'| at S0
    c = rnd(ev(P, S0), 10 ** 32)
    etaw = etaw + abs(ev(P, S0) - c)
    e0 = rnd(T6v(c), SDEN)
    f0 = rnd(ev(Pd, S0), SDEN)
    # |exp w - exp c| <= exp(|c| + etaw) etaw <= 2 etaw ; |exp c - T6(c)| <= |c|^6 7/4320
    dE = 2 * etaw + abs(c) ** 6 * F(7, 4320) + abs(T6v(c) - e0)
    dF = dphi + abs(ev(Pd, S0) - f0)
    delta = ceil_q(max(dE, dF), 10 ** 40)
    return dict(L=L, eta=eta, C=C, etaw=etaw, dphi=dphi, c=c, e0=e0, f0=f0, delta=delta)


def taylor(t0, e0, f0):
    E, Ph = [e0], [f0]
    for k in range(N):
        # E_{k+1} = (sum_{i<=k} E_i Ph_{k-i}) / (k+1)
        E.append(sum(E[i] * Ph[k - i] for i in range(k + 1)) / (k + 1))
        ek1 = E[k - 1] if k >= 1 else F(0)
        Ph.append(-((k + 2) * Ph[k] + t0 * E[k] + ek1) / (t0 * (k + 1)))
    return [e0] + [rnd(c, DEN) for c in E[1:]], [f0] + [rnd(c, DEN) for c in Ph[1:]]


def make_grid():
    g = [S0]
    t = S0
    while t < A:
        K = 2 / t + 1 + F(1, 10)
        h = KH / K
        # round h down to a simple fraction
        h = F(math.floor(h * 1024), 1024) if h > F(1, 1024) else F(math.floor(h * 2 ** 20), 2 ** 20)
        if t < C_DEC <= t + h:
            h = C_DEC - t
        if t + h >= A or A - (t + h) < h / 4:
            h = A - t
        t = t + h
        g.append(t)
    g.append(B)
    return g


def run(verbose=True):
    P, Pd, W, rho, R, Mp, Rr = start()
    sb = startbox(P, Pd, W, rho, R, Mp)
    e0, f0, delta = sb['e0'], sb['f0'], sb['delta']
    if verbose:
        print('start: R', float(R), 'Mp', float(Mp), 'eta', float(sb['eta']), 'delta0',
              float(delta), file=sys.stderr)
    grid = make_grid()
    cells = []
    for i in range(len(grid) - 1):
        t0, h = grid[i], grid[i + 1] - grid[i]
        pe, pp = taylor(t0, e0, f0)
        EH = ceil_q(max(abs(lowb(pe, h)), abs(upb(pe, h))) + M + F(1, 10 ** 6), 10 ** 6)
        PH = ceil_q(max(abs(lowb(pp, h)), abs(upb(pp, h))) + M + F(1, 10 ** 6), 10 ** 6)
        K = max(F(1), PH + EH, ceil_q(2 / t0 + 1, 10 ** 6))
        assert K * h < 1, (i, float(K * h))
        Eg = 1 / (1 - K * h)
        d1 = add(deriv(pe), sc(-1, mul(pe, pp)))
        s = [t0, F(1)]
        d2 = add(mul(s, deriv(pp)), sc(2, pp), mul(s, pe))
        eps = ceil_q(max(absb(d1, h), absb(d2, h) / t0))
        Bc = ceil_q(delta * Eg + eps / K * (Eg - 1))
        assert Bc < M
        ee, fe = ev(pe, h), ev(pp, h)
        ne, nf = rnd(ee, SDEN), rnd(fe, SDEN)
        nd = ceil_q(Bc + max(abs(ee - ne), abs(fe - nf)))
        kind = 'pos' if t0 + h <= C_DEC else 'dec'
        cells.append(dict(i=i, t0=t0, h=h, pe=pe, pp=pp, d1=d1, d2=d2, eps=eps, delta=delta,
                          B=Bc, K=K, EH=EH, PH=PH, ne=ne, nf=nf, nd=nd, kind=kind))
        e0, f0, delta = ne, nf, nd
    return dict(P=P, Pd=Pd, W=W, rho=rho, R=R, Mp=Mp, Rr=Rr, sb=sb, cells=cells)


def pos_poly(c):
    return add([F(2)], mul([c['t0'], F(1)], c['pp']))


def dec_poly(c):
    return add(c['pp'], mul([c['t0'], F(1)], c['pe']))


if __name__ == '__main__':
    out = run()
    cells = out['cells']
    for c in cells[::10] + cells[-3:]:
        print(c['i'], float(c['t0']), float(c['h']), 'K', float(c['K']), 'eps', float(c['eps']),
              'B', float(c['B']), c['kind'], file=sys.stderr)
    for c in cells:
        t1 = c['t0'] + c['h']
        if c['kind'] == 'pos':
            m = lowb(pos_poly(c), c['h']) - t1 * c['B']
        else:
            m = lowb(dec_poly(c), c['h']) - (1 + t1) * c['B']
        if m <= 0:
            print('FAIL margin', c['i'], c['kind'], float(c['t0']), float(m), file=sys.stderr)
    last = cells[-1]
    a, d = last['t0'], last['delta']
    pa = 2 + a * last['pp'][0]
    print('p(a) =', float(pa), '+-', float(a * d), file=sys.stderr)
    pb = 2 + B * (ev(last['pp'], last['h']) + last['B'])
    print('p(b) <=', float(pb), file=sys.stderr)
    L1 = a ** 2 * (last['pe'][0] - d)
    L2 = a ** 2 * (last['pe'][0] + d)
    Pa = abs(pa) + a * d
    hi = L2 + Pa ** 2 / (2 * (1 - 2 / L1))
    print('lambda in', float(L1), float(hi), 'margins', float(L1 - F(3321992118, 10 ** 9)),
          float(F(3321992119, 10 ** 9) - hi), file=sys.stderr)
    print('cells', len(cells), 'final delta', float(d), file=sys.stderr)
