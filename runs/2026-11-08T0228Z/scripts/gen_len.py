"""Certificate generator for the Lane-Emden enclosure of integer index NIDX (run 2026-11-08T0228Z;
generalised from runs/2026-11-05T0028Z/scripts/gen_le.py, n = 3 there).

usage: gen_len.py <n> [out.json]   (window A_LO, A_HI and grid from the table WIN below)

theta' = phi, phi' = -(2/xi) phi - theta^n on [XI0, end], exact rational arithmetic only.
Start box at XI0 from the singular-start lemma: every solution has |theta - P| <= ETA and
|phi - P'| <= XI0/3 (L ETA + R) on (0, XI0], P = truncated Taylor series (rational).
Cells [t0, t0 + h]: Taylor polynomials in sigma = xi - t0 through the rounded state,
coefficients rounded to 1/DEN. Defects:
  D1 = p_theta' - p_phi,  D2 = (t0 + s) p_phi' + 2 p_phi + (t0 + s) p_theta^n (polynomials);
  eps >= max(sum|D1_k| h^k, sum|D2_k| h^k / t0).
Lipschitz on the slab |theta| <= TH (per cell): K = max(1, 2/t0 + 3 TH^2) (sup norm).
Tube: |p_theta| <= TH - M on the cell (crude bounds).  Groenwall: B = delta E + eps/K (E - 1),
E = 1/(1 - K h).  Next state rounded to 1/SDEN.
"""
from fractions import Fraction as F
import math, sys, json

N = 10
DEN = 10 ** 16
SDEN = 10 ** 16
M = F(1, 100)
XI0 = F(1, 2)
KSER = 13          # start polynomial P = sum_{k <= KSER} a_k xi^(2k)
PDEN = 10 ** 22

NIDX = int(sys.argv[1])
WIN = {2: (F(43528745959, 10 ** 10), F(43528745960, 10 ** 10)),
       3: (F(6896848615, 10 ** 9), F(6896848625, 10 ** 9)),
       4: (F(14971546340, 10 ** 9), F(14971546360, 10 ** 9))}
A_LO, A_HI = WIN[NIDX]   # xi_1 window


def rnd(q, d):
    return F(round(q * d), d)


def ceil_q(q, d=10 ** 22):
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


def pw(p, n):
    r = [F(1)]
    for _ in range(n):
        r = mul(r, p)
    return r


def trunc(p, n):
    return p[:n]


# ---- series at 0 (exact) ----
def series(K):
    a = [F(1)]
    for k in range(1, K + 1):
        c3 = pw(a[:k], NIDX)
        a.append(-c3[k - 1] / (2 * k * (2 * k + 1)))
    return a


def start():
    a = series(KSER)
    P = [F(0)] * (2 * KSER + 1)
    for k, ak in enumerate(a):
        P[2 * k] = ak if k == 0 else rnd(ak, PDEN)
    Pd = deriv(P)
    # w = (xi^2 P')' ;  residual r = w + xi^2 P^3 = xi^2 rho
    x2 = [F(0), F(0), F(1)]
    w = deriv(mul(x2, Pd))
    r = add(w, mul(x2, pw(P, NIDX)))
    assert r[0] == 0 and r[1] == 0
    rho = r[2:]
    R = ceil_q(absb(rho, XI0))
    Mp = ceil_q(absb(P, XI0), 10 ** 6)       # |P| <= Mp on [0, XI0]
    return P, Pd, rho, R, Mp


def startbox(P, Pd, rho, R, Mp):
    # choose eta: need XI0^2/6 (L eta + R) < eta, L = 3 (Mp + eta)^2 (use eta <= 1/1000)
    L = ceil_q(NIDX * (Mp + F(1, 1000)) ** (NIDX - 1), 10 ** 6)
    alpha = XI0 ** 2 / 6 * L
    assert alpha < 1
    eta = ceil_q(2 * (XI0 ** 2 / 6 * R) / (1 - alpha), 10 ** 30)
    eta = max(eta, F(1, 10 ** 28))
    assert XI0 ** 2 / 6 * (L * eta + R) < eta and eta <= F(1, 1000)
    dphi = ceil_q(XI0 / 3 * (L * eta + R), 10 ** 30)
    return L, eta, dphi


def taylor(t0, th0, ph0):
    th, ph = [th0], [ph0]
    for k in range(N):
        # c = theta^n coefficients up to k
        c3 = pw(th[:k + 1], NIDX)
        th.append(ph[k] / (k + 1))
        ck1 = c3[k - 1] if k >= 1 else F(0)
        ph.append((-(k + 2) * ph[k] - t0 * c3[k] - ck1) / (t0 * (k + 1)))
    return [th0] + [rnd(c, DEN) for c in th[1:]], [ph0] + [rnd(c, DEN) for c in ph[1:]]


def make_grid():
    g = [XI0]
    t = XI0
    while t < min(F(6, 1), A_LO - 1):
        h = F(1, 40) if t < 1 else F(1, 20) if t < 2 else F(1, 10)
        t += h
        g.append(t)
    while t + F(1, 10) < A_LO:
        t += F(1, 10)
        g.append(t)
    g.append(A_LO)
    g.append(A_HI)
    return g


def run(verbose=True):
    P, Pd, rho, R, Mp = start()
    L, eta, dphi = startbox(P, Pd, rho, R, Mp)
    th0 = rnd(ev(P, XI0), SDEN)
    ph0 = rnd(ev(Pd, XI0), SDEN)
    delta = ceil_q(max(eta + abs(ev(P, XI0) - th0), dphi + abs(ev(Pd, XI0) - ph0)), 10 ** 30)
    if verbose:
        print('start: R', float(R), 'Mp', float(Mp), 'L', float(L), 'eta', float(eta),
              'dphi', float(dphi), 'delta0', float(delta), file=sys.stderr)
    grid = make_grid()
    cells = []
    for i in range(len(grid) - 1):
        t0, h = grid[i], grid[i + 1] - grid[i]
        pt, pp = taylor(t0, th0, ph0)
        TH = ceil_q(max(abs(lowb(pt, h)), abs(upb(pt, h))) + M + F(1, 10 ** 6), 10 ** 6)
        K = max(F(1), ceil_q(2 / t0 + NIDX * TH ** (NIDX - 1), 10 ** 6))
        assert K * h < 1, (i, float(K * h))
        E = 1 / (1 - K * h)
        d1 = add(deriv(pt), sc(-1, pp))
        s = [t0, F(1)]
        d2 = add(mul(s, deriv(pp)), sc(2, pp), mul(s, pw(pt, NIDX)))
        eps = ceil_q(max(absb(d1, h), absb(d2, h) / t0))
        B = ceil_q(delta * E + eps / K * (E - 1))
        assert B < M
        te, pe = ev(pt, h), ev(pp, h)
        nt, np_ = rnd(te, SDEN), rnd(pe, SDEN)
        nd = ceil_q(B + max(abs(te - nt), abs(pe - np_)))
        cells.append(dict(i=i, t0=t0, h=h, pt=pt, pp=pp, d1=d1, d2=d2, eps=eps, delta=delta,
                          B=B, K=K, TH=TH, nt=nt, np=np_, nd=nd))
        th0, ph0, delta = nt, np_, nd
    return dict(P=P, Pd=Pd, rho=rho, R=R, Mp=Mp, L=L, eta=eta, dphi=dphi, cells=cells)


if __name__ == '__main__':
    out = run()
    cells = out['cells']
    for c in cells[::10] + cells[-3:]:
        print(c['i'], float(c['t0']), 'K', float(c['K']), 'eps', float(c['eps']),
              'B', float(c['B']), file=sys.stderr)
    # positivity margins up to A_LO, sign at A_HI
    worst = max(float(upb(c['pp'], c['h']) + c['B']) for c in cells)
    print('max phi upper bound (must be < 0)', worst, file=sys.stderr)
    assert worst < 0
    last = cells[-1]
    print('theta(A_LO) in', float(last['pt'][0] - last['delta']), float(last['pt'][0] + last['delta']),
          file=sys.stderr)
    print('theta(A_HI) <=', float(ev(last['pt'], last['h']) + last['B']), file=sys.stderr)
    print('phi on last cell <=', float(upb(last['pp'], last['h']) + last['B']), file=sys.stderr)
    print('cells', len(cells), file=sys.stderr)
    if len(sys.argv) > 2:
        def ser(v):
            if isinstance(v, F):
                return str(v)
            if isinstance(v, list):
                return [str(a) for a in v]
            return v
        json.dump({k: (ser(v) if k != 'cells' else [{kk: ser(vv) for kk, vv in c.items()} for c in v])
                   for k, v in out.items()}, open(sys.argv[2], 'w'))
