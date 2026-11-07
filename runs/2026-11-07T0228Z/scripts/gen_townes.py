"""Certificate generator for the Townes shooting events (run 2026-11-07T0228Z).

Radial ground-state equation in the plane: theta'' + (1/xi) theta' - theta + theta^3 = 0,
theta(0) = C, theta'(0) = 0.  System theta' = phi, phi' = -(1/xi) phi + theta - theta^3.
Exact rational arithmetic only (template: runs/2026-11-05T0028Z/scripts/gen_le.py).

Singular start on (0, XI0]: u = xi (phi - P'), u' = xi (g(theta) - g(P)) - xi rho, g(x) = x - x^3,
|g(a) - g(b)| <= L |a - b| with L = 1 + 3 (Mp + eta)^2; gives
|phi - P'| <= xi/2 (L eta + R), |theta - P| <= xi^2/4 (L eta + R)  (need XI0^2/4 (L eta + R) < eta).
Residual: (xi P')' - xi (P - P^3) = xi rho  (rho polynomial, |rho| <= R on [0, XI0]).
Cells [t0, t0 + h]: Taylor polynomials in sigma = xi - t0, coefficients rounded to 1/DEN. Defects:
  D1 = p_theta' - p_phi,
  D2 = (t0 + s) p_phi' + p_phi - (t0 + s)(p_theta - p_theta^3);
  eps >= max(sum|D1_k| h^k, sum|D2_k| h^k / t0).
Lipschitz on the slab |theta| <= TH: K = max(1, 1/t0 + 1 + 3 TH^2) (sup norm).
Groenwall per cell: B = delta E + eps/K (E - 1), E = 1/(1 - K h).

Usage: gen_townes.py <C numerator> <C denominator> <mode: over|under> [json-out]
  over : certify phi < 0 on (0, end] and theta(end) < 0 (theta crosses zero while decreasing);
  under: certify theta > 0 on [0, end] and phi(end) > 0 (phi turns positive before a zero).
"""
from fractions import Fraction as F
import math, sys, json

N = 12
DEN = 10 ** 20
SDEN = 10 ** 20
M = F(1, 100)
XI0 = F(3, 10)
KSER = 22          # start polynomial P = sum_{k <= KSER} a_k xi^(2k)
PDEN = 10 ** 26


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


def series(C, K):
    # a_k (2k)^2 = [Q - Q^3]_{k-1}
    a = [F(C)]
    for k in range(1, K + 1):
        sq = [sum(a[i] * a[j - i] for i in range(j + 1)) for j in range(k)]
        c3 = [sum(sq[i] * a[j - i] for i in range(j + 1)) for j in range(k)]
        a.append((a[k - 1] - c3[k - 1]) / (2 * k) ** 2)
    return a


def start(C):
    a = series(C, KSER)
    P = [F(0)] * (2 * KSER + 1)
    for k, ak in enumerate(a):
        P[2 * k] = ak if k == 0 else rnd(ak, PDEN)
    Pd = deriv(P)
    x1 = [F(0), F(1)]
    w = deriv(mul(x1, Pd))                    # (xi P')'
    g = add(P, sc(-1, mul(P, mul(P, P))))     # P - P^3
    r = add(w, sc(-1, mul(x1, g)))            # = xi rho
    assert r[0] == 0
    rho = r[1:]
    R = ceil_q(absb(rho, XI0))
    Mp = ceil_q(absb(P, XI0), 10 ** 6)
    return P, Pd, w, rho, R, Mp


def startbox(R, Mp):
    L = ceil_q(1 + 3 * (Mp + F(1, 1000)) ** 2, 10 ** 6)
    alpha = XI0 ** 2 / 4 * L
    assert alpha < 1
    eta = ceil_q(2 * (XI0 ** 2 / 4 * R) / (1 - alpha), 10 ** 34)
    eta = max(eta, F(1, 10 ** 32))
    assert XI0 ** 2 / 4 * (L * eta + R) < eta and eta <= F(1, 1000)
    dphi = ceil_q(XI0 / 2 * (L * eta + R), 10 ** 34)
    return L, eta, dphi


def taylor(t0, th0, ph0):
    th, ph = [th0], [ph0]
    for k in range(N):
        sq = [sum(th[i] * th[j - i] for i in range(j + 1)) for j in range(k + 1)]
        c3 = [sum(sq[i] * th[j - i] for i in range(j + 1)) for j in range(k + 1)]
        gk = th[k] - c3[k]
        gk1 = (th[k - 1] - c3[k - 1]) if k >= 1 else F(0)
        th.append(ph[k] / (k + 1))
        ph.append((t0 * gk + gk1 - (k + 1) * ph[k]) / (t0 * (k + 1)))
    return [th0] + [rnd(c, DEN) for c in th[1:]], [ph0] + [rnd(c, DEN) for c in ph[1:]]


def run(C, mode, end=None, verbose=True):
    P, Pd, w, rho, R, Mp = start(C)
    L, eta, dphi = startbox(R, Mp)
    th0 = rnd(ev(P, XI0), SDEN)
    ph0 = rnd(ev(Pd, XI0), SDEN)
    d0 = XI0 ** 2 / 4 * (L * eta + R)
    delta = ceil_q(max(d0 + abs(ev(P, XI0) - th0), dphi + abs(ev(Pd, XI0) - ph0)), 10 ** 34)
    if verbose:
        print('start: R', float(R), 'Mp', float(Mp), 'L', float(L), 'eta', float(eta),
              'dphi', float(dphi), 'delta0', float(delta), file=sys.stderr)
    cells = []
    t = XI0
    stop = None
    while True:
        h = F(1, 50) if t < 1 else F(1, 20) if t < 2 else F(1, 10) if t < 4 else F(1, 5)
        t0 = t
        pt, pp = taylor(t0, th0, ph0)
        TH = ceil_q(max(abs(lowb(pt, h)), abs(upb(pt, h))) + M + F(1, 10 ** 6), 10 ** 6)
        K = max(F(1), ceil_q(1 / t0 + 1 + 3 * TH ** 2, 10 ** 6))
        assert K * h < 1, (len(cells), float(K * h))
        E = 1 / (1 - K * h)
        d1 = add(deriv(pt), sc(-1, pp))
        s = [t0, F(1)]
        gpt = add(pt, sc(-1, mul(pt, mul(pt, pt))))
        d2 = add(mul(s, deriv(pp)), pp, sc(-1, mul(s, gpt)))
        eps = ceil_q(max(absb(d1, h), absb(d2, h) / t0))
        B = ceil_q(delta * E + eps / K * (E - 1))
        assert B < M, (len(cells), float(t0), float(B))
        te, pe = ev(pt, h), ev(pp, h)
        nt, np_ = rnd(te, SDEN), rnd(pe, SDEN)
        nd = ceil_q(B + max(abs(te - nt), abs(pe - np_)))
        c = dict(i=len(cells), t0=t0, h=h, pt=pt, pp=pp, d1=d1, d2=d2, eps=eps, delta=delta,
                 B=B, K=K, TH=TH, nt=nt, np=np_, nd=nd)
        cells.append(c)
        th0, ph0, delta = nt, np_, nd
        t = t0 + h
        # event checks at the cell end (state enclosure nt +- nd)
        if mode == 'over':
            assert upb(pp, h) + B < 0, ('phi not certified negative', len(cells), float(t0),
                                        float(upb(pp, h)), float(B))
            if nt + nd < 0:
                stop = t
                break
        else:
            assert lowb(pt, h) - B > 0, ('theta not certified positive', len(cells), float(t0),
                                         float(lowb(pt, h)), float(B))
            if np_ - nd > 0:
                stop = t
                break
        if t > 30:
            raise SystemExit('no event by 30')
    return dict(C=F(C), mode=mode, P=P, Pd=Pd, W=w, rho=rho, R=R, Mp=Mp, L=L, eta=eta,
                dphi=dphi, cells=cells, stop=stop)


if __name__ == '__main__':
    C = F(int(sys.argv[1]), int(sys.argv[2]))
    mode = sys.argv[3]
    out = run(C, mode)
    cells = out['cells']
    for c in cells[::10] + cells[-2:]:
        print(c['i'], float(c['t0']), 'K', float(c['K']), 'eps', float(c['eps']),
              'B', float(c['B']), 'th', float(c['nt']), 'ph', float(c['np']), file=sys.stderr)
    print('event at', float(out['stop']), 'cells', len(cells), file=sys.stderr)
    if len(sys.argv) > 4:
        def ser(v):
            if isinstance(v, F):
                return str(v)
            if isinstance(v, list):
                return [str(a) for a in v]
            return v
        json.dump({k: (ser(v) if k != 'cells' else [{kk: ser(vv) for kk, vv in c.items()} for c in v])
                   for k, v in out.items()}, open(sys.argv[4], 'w'))
