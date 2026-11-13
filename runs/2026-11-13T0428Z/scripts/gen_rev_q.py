# Run 2026-11-13T0428Z: copy of runs/2026-11-13T0228Z/scripts/gen_rev_p.py with an exact sqrt_up (see there). That file was: # Run 2026-11-13T0228Z: copy of runs/2026-11-11T1228Z/scripts/gen_rev.py with one progress line every 16 cells (flushed),
# so a long chain shows where it is (run 0228Z waited > 75 min on two chains with empty logs). Output unchanged otherwise.
#!/usr/bin/env python3
"""Run 2026-11-11T1228Z: copy of runs/2026-11-09T1228Z/scripts/gen_low.py with the slow threshold THETA = env FS_THETA (default 11/30; 11/15 for K >= 5), the slowL end check 1/3 < p - r2 (as Lean endSL) and the optional fine start FS_HFINE of runs/2026-11-11T0828Z/scripts/gen_neg_wc_theta.py. Run 2026-11-09T1228Z variant (lower, reversed-flow branch): modes slowL (per cell p + r2 < 1 only; at the end 0 < p - r2, 0 < q - B, q + B < 3(1 - (p + r2)), g - r1 > 11/30) and tube (initial ball radius R0 = env FS_R0 around (0, 0, A); per cell -1/2 < p - r2; at the end 0 < g - r1, 0 < p - r2, p + r2 < 1, 0 < q - B). Base: run 2026-11-09T0828Z: ADVERSE-SIGN port of runs/2026-11-08T2028Z/scripts/gen_k_wc.py: field g''' + K g g'' - 1 + g'^2 = 0
(F3 = -K y1 y3 + 1 - y2^2); one-sided corners with s = -(y2 + P2); modes over / slow (slow: per cell p + r2 < 1 and q - B > 0;
at the end 0 <= p - r2, q + B < 3(1 - (p + r2)), g - r1 > 11/30). Original docstring follows.
CLAMPED variant (CellProp also checks the ball inside the clamps |g| < t0 + 2, |p| < 2, |q| < 2,
as runs/2026-11-08T0428Z/scripts/gen_homann_wc.py). K-parameterised copy (K = env FS_K, a rational; Falkner-Skan beta = 1/K after scaling) of
runs/2026-11-08T0428Z/scripts/gen_homann_w.py, itself (from runs/2026-11-07T2028Z/scripts/gen_hiemenz_w.py with K = 2): exact-rational
validated cells for the Homann (axisymmetric stagnation-point) initial-value problem
g''' + 2 g g'' + 1 - g'^2 = 0, g(0) = g'(0) = 0, g''(0) = A on [0, L], in the
weighted norm V(e) = w1 e1^2 + w2 e2^2 + e3^2 with a one-sided bound mu per cell (pattern of
runs/2026-11-07T1628Z/scripts/gen_blasius_w.py).

One-sided bound: with F3(y) = -2 y1 y3 - 1 + y2^2 and P the approximation,
  mu V(e) - <F(y) - F(P), e>_W = e^T M e + (2 y1 - m) e3^2,
  M = [[mu w1, -w1/2, (2 P3)/2], [-w1/2, mu w2, -(w2+s)/2], [(2 P3)/2, -(w2+s)/2, mu+m]],
with m = 2 * (lower bound of g on the ball) and the P3-corners doubled (Lean: psdOK at 2*mlo, 2*qlo, 2*qhi).
with s = y2 + P2 in [slo, shi] (P2's range on the cell -/+ r2) and P3 in [qlo, qhi]; M is affine in
(P3, s), so positive semidefiniteness at the four corners suffices (Sylvester, as psdOK).

Also checks along the chain the sign conditions of the two shooting events:
  mode 'under': every cell's p-range upper end + r2 < 1, and at the end q + B < 0;
  mode 'over' : every cell's q-range lower end - B > 0, and at the end p - r2 > 1.
usage: gen_hiemenz_w.py A L h_den N digits w1 w2 mode out.json"""
import sys, json, math, os
from fractions import Fraction as Fr
K = Fr(os.environ["FS_K"])
THETA = Fr(os.environ.get("FS_THETA", "11/30"))

def qadd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def qsmul(c, p): return [c * x for x in p]
def qsub(p, q): return qadd(p, qsmul(-1, q))
def qmul(p, q):
    if not p or not q: return []
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): r[i + j] += a * b
    return r
def qderiv(p): return [p[k] * k for k in range(1, len(p))]
def qeval(p, x):
    r = Fr(0)
    for c in reversed(p): r = r * x + c
    return r
def qabs(p, h): return qeval([abs(c) for c in p], h)
def head(p): return p[0] if p else Fr(0)
def rnd(x, D): return Fr(round(x * D), D)
def up(x, D):
    n = x * D
    return Fr(-((-n.numerator) // n.denominator), D)
def sqrt_up(x, D):
    # Run 2026-11-13T0428Z: exact integer square root. The float start plus a linear walk in steps of 1/D took
    # up to ~1e8 steps per call once r1, r2 exceeded ~1e-8 (float error 1e-16 relative vs D = 1e29): run 0228Z's
    # chains stalled for > 75 min at cell ~120. Result: the least s = k/D with s*s >= x (the old one was some s >= it).
    if x <= 0: return Fr(0)
    M = -((-x.numerator * D * D) // x.denominator)
    k = math.isqrt(M - 1) + 1
    s = Fr(k, D)
    assert s * s >= x and (k == 0 or Fr(k - 1, D) ** 2 < x)
    return s

def taylor(a, b, c, N, D):
    g, p, q = [a], [b], [c]
    for k in range(N):
        conv = K * sum(g[i] * q[k - i] for i in range(k + 1))
        pp = sum(p[i] * p[k - i] for i in range(k + 1))
        g.append(rnd(p[k] / (k + 1), D)); p.append(rnd(q[k] / (k + 1), D))
        q.append(rnd((-conv + (1 if k == 0 else 0) - pp) / (k + 1), D))
    return g, p, q

def defects(pg, pp, pq):
    d3 = qadd(qsub(qadd(qderiv(pq), qmul(qsmul(K, pg), pq)), [Fr(1)]), qmul(pp, pp))
    return (qsub(qderiv(pg), pp), qsub(qderiv(pp), pq), d3)

def det3(m11, m12, m13, m22, m23, m33):
    return m11 * (m22 * m33 - m23 ** 2) - m12 * (m12 * m33 - m23 * m13) + m13 * (m12 * m23 - m22 * m13)

def psd(mu, w1, w2, m, P3, s):
    m11, m12, m13, m22, m23, m33 = mu * w1, -w1 / 2, P3 / 2, mu * w2, -(w2 + s) / 2, mu + m
    return m11 > 0 and m11 * m22 - m12 ** 2 > 0 and det3(m11, m12, m13, m22, m23, m33) >= 0

def rng(p, h): return head(p) - h * qabs(p[1:], h), head(p) + h * qabs(p[1:], h)

def corners(c):
    h, r2 = c['h'], c['r2']
    ql, qh = rng(c['pq'], h); pl, ph = rng(c['pp'], h)
    m = K * (rng(c['pg'], h)[0] - c['r1'])
    return m, [(P3, s) for P3 in (K * ql, K * qh) for s in (-(2 * ph + r2), -(2 * pl - r2))]

def cellprop(T, c):
    t0, h, d, e, B, mu, w1, w2, r1, r2 = (c[k] for k in ('t0', 'h', 'δ', 'ε', 'B', 'μ', 'w1', 'w2', 'r1', 'r2'))
    d1, d2, d3 = defects(c['pg'], c['pp'], c['pq'])
    E1, E2, E3 = qabs(d1, h), qabs(d2, h), qabs(d3, h)
    m, cs = corners(c)
    conds = [0 <= t0, t0 + h <= T, 0 < h, 0 < w1, 0 < w2, 0 <= mu, mu * h < 1, 0 < d, 0 < e,
             w1 * E1 ** 2 + w2 * E2 ** 2 + E3 ** 2 < e ** 2, 0 <= r1, B ** 2 <= w1 * r1 ** 2,
             0 <= r2, B ** 2 <= w2 * r2 ** 2] + [psd(mu, w1, w2, m, P3, s) for P3, s in cs] + \
            [(d + e * h) / (1 - mu * h) <= B]
    gl, gh = rng(c['pg'], h); pl, ph = rng(c['pp'], h); ql, qh = rng(c['pq'], h)
    conds += [-(t0 + 2) < gl - r1, gh + r1 < t0 + 2, -2 < pl - r2, ph + r2 < 2, -2 < ql - B, qh + B < 2]
    return all(conds), conds

def min_mu(w1, w2, m, cs, den=10000):
    ok = lambda mu: all(psd(mu, w1, w2, m, P3, s) for P3, s in cs)
    lo, hi = Fr(0), Fr(1)
    while not ok(hi): hi *= 2
    for _ in range(40):
        mid = (lo + hi) / 2
        if ok(mid): hi = mid
        else: lo = mid
    return up(hi, den)

def main():
    A = Fr(sys.argv[1]); L = Fr(sys.argv[2]); h = Fr(1, int(sys.argv[3])); N = int(sys.argv[4])
    D = 10 ** int(sys.argv[5]); w1 = Fr(sys.argv[6]); w2 = Fr(sys.argv[7]); mode = sys.argv[8]; out = sys.argv[9]
    RD = D * 1000
    cells = []
    a, b, c, delta = Fr(0), Fr(0), A, Fr(1, RD) + Fr(os.environ.get('FS_R0', '0'))
    t0 = Fr(0); amp_log = 0.0; margin = None
    h0 = h
    hf, tf = (Fr(1, int(os.environ['FS_HFINE'].split(':')[0])), Fr(os.environ['FS_HFINE'].split(':')[1])) if 'FS_HFINE' in os.environ else (h, Fr(0))
    while t0 < L:
        h = hf if t0 < tf else h0
        pg, pp, pq = taylor(a, b, c, N, D)
        d1, d2, d3 = defects(pg, pp, pq)
        E1, E2, E3 = qabs(d1, h), qabs(d2, h), qabs(d3, h)
        eps = sqrt_up(w1 * E1 ** 2 + w2 * E2 ** 2 + E3 ** 2, RD) + Fr(1, RD)
        B = (delta + eps * h) * 2
        cell = {'t0': t0, 'h': h, 'δ': delta, 'ε': eps, 'w1': w1, 'w2': w2, 'pg': pg, 'pp': pp, 'pq': pq}
        for _ in range(30):
            cell['B'] = B; cell['r1'] = sqrt_up(B ** 2 / w1, RD); cell['r2'] = sqrt_up(B ** 2 / w2, RD)
            m, cs = corners(cell)
            mu = min_mu(w1, w2, m, cs)
            assert mu * h < 1, (float(t0), float(mu))
            Bn = up((delta + eps * h) / (1 - mu * h), RD)
            if Bn <= B: B = Bn; break
            B = Bn
        cell['B'] = B; cell['r1'] = sqrt_up(B ** 2 / w1, RD); cell['r2'] = sqrt_up(B ** 2 / w2, RD)
        m, cs = corners(cell); cell['μ'] = min_mu(w1, w2, m, cs)
        ok, conds = cellprop(L, cell)
        assert ok, (float(t0), [i for i, x in enumerate(conds) if not x])
        if mode == 'slow': mg = min(1 - (rng(pp, h)[1] + cell['r2']), rng(pq, h)[0] - B)
        elif mode == 'slowL': mg = 1 - (rng(pp, h)[1] + cell['r2'])
        elif mode == 'tube': mg = rng(pp, h)[0] - cell['r2'] + Fr(1, 2)
        else: mg = Fr(1)
        margin = mg if margin is None else min(margin, mg)
        cells.append(cell); amp_log += float(cell['μ'] * h)
        if len(cells) % 16 == 0: print('progress cells', len(cells), 't0 %.4f' % float(t0), 'amp e^%.2f' % amp_log, flush=True)
        ea, eb, ec = qeval(pg, h), qeval(pp, h), qeval(pq, h)
        a, b, c = rnd(ea, D), rnd(eb, D), rnd(ec, D)
        s = sqrt_up(w1 * (ea - a) ** 2 + w2 * (eb - b) ** 2 + (ec - c) ** 2, RD)
        delta = B + s
        t0 += h
    last = cells[-1]
    eg, ep, eq = (qeval(last[k], last['h']) for k in ('pg', 'pp', 'pq'))
    B, r2 = last['B'], last['r2']
    r1 = last['r1']
    if mode == 'slow': endm = min(ep - r2, 3 * (1 - (ep + r2)) - (eq + B), eg - r1 - THETA)
    elif mode == 'slowL': endm = min(ep - r2 - Fr(1, 3), eq - B, 3 * (1 - (ep + r2)) - (eq + B), eg - r1 - THETA)
    elif mode == 'tube': endm = min(eg - r1, 1 - (eg + r1), ep - r2, 1 - (ep + r2), eq - B, Fr(6, 5) - (eq + B))
    else: endm = ep - r2 - 1
    print('end state g p q', float(eg), float(ep), float(eq), 'B', float(B))
    pass
    print('cells', len(cells), 'final B %.3g' % float(B), 'r2 %.3g' % float(r2), 'amp e^%.2f' % amp_log,
          'end g p q', float(eg), float(ep), float(eq), 'max eps %.3g' % max(float(x['ε']) for x in cells),
          'mode', mode, 'path margin %.3g' % float(margin), 'end margin %.3g' % float(endm),
          'OK' if margin > 0 and endm > 0 else 'FAIL')
    ser = lambda x: [x.numerator, x.denominator]
    json.dump({'A': ser(A), 'L': ser(L), 'mode': mode,
               'cells': [{k: ([ser(y) for y in v] if isinstance(v, list) else ser(v)) for k, v in cl.items()} for cl in cells]},
              open(out, 'w'))

if __name__ == '__main__':
    main()
