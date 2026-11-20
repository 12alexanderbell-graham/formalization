"""Certificate generator for the Lane-Emden enclosure of index 9/2 (run 2026-11-20T0428Z; from gen_le72.py of run 2026-11-19T2228Z).

theta' = phi, phi' = -(2/xi) phi - g(theta), g(x) = sqrt(max(x,0))^9, on [XI0, A_HI].
Exact rational checks mirror Work/Math/LE92CellQ.lean (CellProp, GamProp) and the start lemma
Work/Math/LEGStart.lean.  Taylor coefficients are computed in mpmath and rounded to 1/DEN; every
inequality the kernel decides is re-checked here in Fractions.

Run 2026-11-20T0428Z: every cell carries a weight w (LE_WST, 'from:w' pairs) and is checked in the
norm max(|dtheta|, w |dphi|) (Work/Math/LE92Cell.lean `cell`): with w = 1 the max norm forces K >= 1
(theta' = phi) and the enclosure grew like e^xi to 3e-4 at the zero near 31.8; with w = 4, 10, 20 from
xi = 4, 8, 16 the end radius is 4e-11 (146 cells).

Cells: mode A (pw = Taylor polynomial of sqrt(theta), certificate |pw^2 - pt| <= eta, pw >= c > 0),
mode B (crude: pw = [], theta^(9/2) of pt bounded by P^9 with pt <= P^2; Taylor of the g-free
equation).  Grid: bulk steps, then geometric steps toward the zero, then one crude cell to A_LO and
the crude last cell [A_LO, A_HI].
"""
from fractions import Fraction as F
import math, sys, json, os
import mpmath as mp
mp.mp.dps = 60

N = int(os.environ.get('LE_N', 12))
DEN = 10 ** int(os.environ.get('LE_DEN', 21))
SDEN = 10 ** int(os.environ.get('LE_SDEN', 21))
PDEN = 10 ** int(os.environ.get('LE_PDEN', 26))
KSER = int(os.environ.get('LE_KSER', 18))
RATIO = int(os.environ.get('LE_RATIO', 5))
DSW = F(os.environ.get('LE_DSW', '1/5'))
M = F(1, 100)
WST = [(F(a), F(b)) for a, b in (x.split(':') for x in os.environ.get('LE_WST', '4:4,8:10,16:20').split(',') if x)]
HB1 = F(os.environ.get('LE_HB1', '3'))
HB2 = F(os.environ.get('LE_HB2', '6'))
HBIG = F(os.environ.get('LE_HBIG', '1/2'))
XI0 = F(1, 2)
A_LO, A_HI = F(os.environ.get('LE_ALO', '318364631/10000000')), F(os.environ.get('LE_AHI', '318364634/10000000'))   # bracket inside the frozen window
XI1 = F('31.83646324469428526438281')    # float reference (ref92.py), only for the grid
W_LO, W_HI = F(os.environ.get('LE_WLO', '1737798864/1000000000')), F(os.environ.get('LE_WHI', '1737798871/1000000000'))   # inside the frozen window


def rnd(q, d):
    return F(round(q * d), d)


def rndm(x, d):   # mpf -> Fraction
    return F(int(mp.nint(x * d)), d)


def ceil_q(q, d=10 ** 22):
    return F(math.ceil(q * d), d)


def floor_q(q, d=10 ** 22):
    return F(math.floor(q * d), d)


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
    if not p or not q:
        return []
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def sc(a, p):
    return [a * c for c in p]


def absb(p, s):   # qabs p s
    return sum(abs(c) * s ** k for k, c in enumerate(p))


def lowb(p, s):   # headD - s * qabs tail s
    if not p:
        return F(0)
    return p[0] - s * absb(p[1:], s)


def upb(p, s):
    if not p:
        return F(0)
    return p[0] + s * absb(p[1:], s)


def sqrt_up(q, d=10 ** 6):
    s = ceil_q(F(mp.nstr(mp.sqrt(mp.mpf(q.numerator) / q.denominator), 40)), d)
    while s * s < q:
        s += F(1, d)
    return s


# ---- start (series at the centre, exact) ----
def powser(a, n):
    """Coefficients of (sum a_k x^k)^n, a_0 = 1 (Miller's recurrence, exact for rational n)."""
    f = [F(1)]
    for m in range(1, len(a)):
        s = F(0)
        for j in range(1, m + 1):
            s += (n * j - m + j) * a[j] * f[m - j]
        f.append(s / m)
    return f


def series(K):
    """theta = sum_k b_k u^k, u = xi^2: b_k = -[theta^(9/2)]_{k-1} / (2k (2k+1))."""
    b = [F(1)]
    for k in range(1, K + 1):
        f = powser(b + [F(0)], F(9, 2))
        b.append(-f[k - 1] / (2 * k * (2 * k + 1)))
    return b


def start():
    b = series(KSER)
    P = [F(0)] * (2 * KSER + 1)
    for k, bk in enumerate(b):
        P[2 * k] = bk if k == 0 else rnd(bk, PDEN)
    sq = powser(b, F(1, 2))
    Pw = [F(0)] * (2 * KSER + 1)
    for k, s in enumerate(sq):
        Pw[2 * k] = s if k == 0 else rnd(s, PDEN)
    Pd = deriv(P)
    x2 = [F(0), F(0), F(1)]
    W = deriv(mul(x2, Pd))
    assert W[0] == 0 and W[1] == 0
    W2 = W[2:]
    rho = add(W2, sept(Pw))
    Rp = ceil_q(absb(rho, XI0))
    c0 = floor_q(lowb(Pw, XI0), 10 ** 6)
    P0 = ceil_q(upb(Pw, XI0), 10 ** 6)
    eta0 = ceil_q(absb(add(mul(Pw, Pw), sc(-1, P)), XI0))
    assert 0 < c0 and eta0 < c0 ** 2
    gam0 = ceil_q(eta0 / c0 * (9 * (P0 ** 2 + eta0) ** 4))
    R = Rp + gam0
    Mp = ceil_q(absb(P, XI0), 10 ** 6)
    return dict(P=P, Pd=Pd, W=W, W2=W2, Pw=Pw, rho=rho, Rp=Rp, c0=c0, P0=P0, eta0=eta0,
                gam0=gam0, R=R, Mp=Mp)


def startbox(st):
    Mp, R = st['Mp'], st['R']
    etaMax = F(1, 1000)
    S = sqrt_up(Mp + etaMax)
    L = ceil_q(F(9, 2) * S ** 7, 10 ** 6)
    alpha = XI0 ** 2 / 6 * L
    assert alpha < 1
    eta = ceil_q(2 * (XI0 ** 2 / 6 * R) / (1 - alpha), 10 ** 30)
    eta = max(eta, F(1, 10 ** 28))
    assert XI0 ** 2 / 6 * (L * eta + R) < eta and eta <= etaMax
    dth = XI0 ** 2 / 6 * (L * eta + R)
    dphi = XI0 / 3 * (L * eta + R)
    return dict(S0=S, L=L, eta=eta, dth=dth, dphi=dphi)


def taylor(t0, th0, ph0, crude):
    t0m = mp.mpf(t0.numerator) / t0.denominator
    a = [mp.mpf(th0.numerator) / th0.denominator]
    b = [mp.mpf(ph0.numerator) / ph0.denominator]
    c = [mp.sqrt(a[0])] if not crude else None
    d = []
    for k in range(N):
        if crude:
            dk = mp.mpf(0); dk1 = mp.mpf(0)
        else:
            # d_k = [w^9]_k
            sq = [sum(c[j] * c[i - j] for j in range(i + 1)) for i in range(k + 1)]
            q4 = [sum(sq[j] * sq[i - j] for j in range(i + 1)) for i in range(k + 1)]
            q8 = [sum(q4[j] * q4[i - j] for j in range(i + 1)) for i in range(k + 1)]
            dk = sum(q8[j] * c[k - j] for j in range(k + 1))
            d.append(dk)
            dk1 = d[k - 1] if k >= 1 else mp.mpf(0)
        a.append(b[k] / (k + 1))
        b.append((-(k + 2) * b[k] - t0m * dk - dk1) / (t0m * (k + 1)))
        if not crude:
            s = sum(c[j] * c[k + 1 - j] for j in range(1, k + 1))
            c.append((a[k + 1] - s) / (2 * c[0]))
    pt = [th0] + [rndm(x, DEN) for x in a[1:]]
    pp = [ph0] + [rndm(x, DEN) for x in b[1:]]
    pw = [] if crude else [rndm(x, DEN) for x in c]
    return pt, pp, pw


def sept(p):   # ninth power (name kept from gen_le72.py)
    p2 = mul(p, p); p4 = mul(p2, p2)
    return mul(mul(p4, p4), p)


def wt(t0):
    w = F(1)
    for a, b in WST:
        if t0 >= a:
            w = b
    return w


def make_cell(t0, h, th0, ph0, delta, crude):
    w = wt(t0)
    pt, pp, pw = taylor(t0, th0, ph0, crude)
    TH = ceil_q(max(abs(lowb(pt, h)), abs(upb(pt, h))) + M + F(1, 10 ** 6), 10 ** 6)
    S = sqrt_up(TH)
    K = max(1 / w, ceil_q(2 / t0 + w * F(9, 2) * S ** 7, 10 ** 6))
    assert K * h < 1, (float(t0), float(K * h))
    if crude:
        up = upb(pt, h)
        P = sqrt_up(max(up, F(0)), 10 ** 12) if up > 0 else F(0)
        c = F(0); eta = F(0)
        gam = ceil_q(P ** 9, 10 ** 30)
    else:
        c = floor_q(lowb(pw, h), 10 ** 12)
        P = ceil_q(upb(pw, h), 10 ** 12)
        eta = ceil_q(absb(add(mul(pw, pw), sc(-1, pt)), h), 10 ** 30)
        assert c > 0 and eta < c ** 2, (float(t0), float(c), float(eta))
        gam = ceil_q(eta / c * (9 * (P ** 2 + eta) ** 4), 10 ** 30)
    d1 = add(deriv(pt), sc(-1, pp))
    s = [t0, F(1)]
    d2 = add(add(mul(s, deriv(pp)), sc(2, pp)), mul(s, sept(pw)))
    eps = ceil_q(max(absb(d1, h), w * (absb(d2, h) + (t0 + h) * gam) / t0), 10 ** 30)
    E = 1 / (1 - K * h)
    B = ceil_q(delta * E + eps / K * (E - 1), 10 ** 30)
    assert B < M, (float(t0), float(h), float(delta), float(eps), float(K))
    cell = dict(w=w, t0=t0, h=h, delta=delta, eps=eps, B=B, TH=TH, K=K, S=S, c=c, P=P, eta=eta,
                gam=gam, pt=pt, pp=pp, pw=pw)
    check_cell(cell, A_HI)
    return cell


def check_cell(c, T):
    """Mirror of CellProp T c (Work/Math/LE92CellQ.lean)."""
    t0, h, pt, pp, pw = c['t0'], c['h'], c['pt'], c['pp'], c['pw']
    K, TH, S = c['K'], c['TH'], c['S']
    w = c['w']
    ok = [0 < w, 0 < t0, t0 + h <= T, 0 < h, 1 <= w * K, 0 <= S, TH <= S ** 2, 2 / t0 + w * F(9, 2) * S ** 7 <= K,
          K * h < 1, 0 <= c['delta'], 0 <= c['eps'],
          -(TH - M) <= lowb(pt, h), upb(pt, h) <= TH - M,
          absb(add(deriv(pt), sc(-1, pp)), h) <= c['eps']]
    s = [t0, F(1)]
    d2 = add(add(mul(s, deriv(pp)), sc(2, pp)), mul(s, sept(pw)))
    ok.append(w * (absb(d2, h) + (t0 + h) * c['gam']) <= c['eps'] * t0)
    if pw == []:
        g = 0 <= c['P'] and upb(pt, h) <= c['P'] ** 2 and c['P'] ** 9 <= c['gam']
    else:
        g = (0 < c['c'] and c['c'] <= lowb(pw, h) and upb(pw, h) <= c['P'] and
             absb(add(mul(pw, pw), sc(-1, pt)), h) <= c['eta'] and c['eta'] < c['c'] ** 2 and
             c['eta'] / c['c'] * (9 * (c['P'] ** 2 + c['eta']) ** 4) <= c['gam'])
    ok.append(g)
    E = 1 / (1 - K * h)
    ok += [c['delta'] * E + c['eps'] / K * (E - 1) <= c['B'], c['B'] < M]
    assert all(ok), [i for i, x in enumerate(ok) if not x]
    return True


def make_grid():
    g = [XI0]
    t = XI0
    while True:
        h = F(1, 40) if t < 1 else F(1, 20) if t < HB1 else F(1, 10) if t < HB2 else HBIG
        if t + h > XI1 - F(1, 5):
            break
        t += h
        g.append(t)
    # geometric approach to the zero (mode A)
    while XI1 - t > DSW:
        h = rnd((XI1 - t) / RATIO, 10 ** 9)
        t += h
        g.append(t)
    g.append(A_LO)
    g.append(A_HI)
    return g


def run(verbose=True):
    st = start()
    sb = startbox(st)
    P, Pd = st['P'], st['Pd']
    th0 = rnd(ev(P, XI0), SDEN)
    ph0 = rnd(ev(Pd, XI0), SDEN)
    delta = ceil_q(max(sb['dth'] + abs(ev(P, XI0) - th0), sb['dphi'] + abs(ev(Pd, XI0) - ph0)), 10 ** 30)
    if verbose:
        print('start: Rp', float(st['Rp']), 'gam0', float(st['gam0']), 'Mp', float(st['Mp']),
              'L', float(sb['L']), 'eta', float(sb['eta']), 'delta0', float(delta), file=sys.stderr)
    grid = make_grid()
    cells = []
    for i in range(len(grid) - 1):
        t0, h = grid[i], grid[i + 1] - grid[i]
        crude = t0 >= grid[-3]
        c = make_cell(t0, h, th0, ph0, delta, crude)
        c['i'] = i
        cells.append(c)
        te, pe = ev(c['pt'], h), ev(c['pp'], h)
        th0, ph0 = rnd(te, SDEN), rnd(pe, SDEN)
        wn = wt(grid[i + 1]) if i + 2 < len(grid) else c['w']
        delta = ceil_q(wn / c['w'] * c['B'] + max(abs(te - th0), wn * abs(pe - ph0)), 10 ** 30)
    return dict(st=st, sb=sb, cells=cells, grid=grid)


def last_check(c):
    t0, h, pt, pp, B, d = c['t0'], c['h'], c['pt'], c['pp'], c['B'], c['delta']
    U = mul(mul([t0, F(1)], [t0, F(1)]), pp)
    Bw = B / c['w']
    r = [0 < pt[0] - d, ev(pt, h) + B < 0, upb(pp, h) + Bw < 0,
         W_LO <= -upb(U, h) - (t0 + h) ** 2 * Bw, -lowb(U, h) + (t0 + h) ** 2 * Bw <= W_HI]
    return r, U


if __name__ == '__main__':
    out = run()
    cells = out['cells']
    for c in cells[::8] + cells[-4:]:
        print(c['i'], 'w', float(c['w']), float(c['t0']), float(c['h']), 'K', float(c['K']), 'eps', float(c['eps']),
              'gam', float(c['gam']), 'B', float(c['B']), file=sys.stderr)
    worst = max(float(upb(c['pp'], c['h']) + c['B'] / c['w']) for c in cells)
    print('max phi upper bound (must be < 0)', worst, file=sys.stderr)
    last = cells[-1]
    r, U = last_check(last)
    print('last checks', r, 'theta(A_LO) >=', float(last['pt'][0] - last['delta']),
          'theta(A_HI) <=', float(ev(last['pt'], last['h']) + last['B']), file=sys.stderr)
    Bw = last['B'] / last['w']
    print('omega in', float(-upb(U, last['h']) - (last['t0'] + last['h']) ** 2 * Bw),
          float(-lowb(U, last['h']) + (last['t0'] + last['h']) ** 2 * Bw), file=sys.stderr)
    print('cells', len(cells), file=sys.stderr)
