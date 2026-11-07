#!/usr/bin/env python3
"""Run 2026-11-07T1628Z: exact-rational validated cells for the Blasius IVP g''' + g g''/2 = 0,
g(0)=g'(0)=0, g''(0)=1 on [0, L], measured in the WEIGHTED norm V(e) = w1 e1^2 + w2 e2^2 + e3^2 with a
one-sided (logarithmic-norm) bound mu per cell, so that the damping term -g q''/2 contracts instead of
being counted as growth (the sup-norm Lipschitz cells of run 1228Z amplified errors ~1e17 over [0, 9];
float study: a constant weight diag(1/10, 1, 1) amplifies ~13). Mirrors `CellPropW` of
Work/Blasius/BCellW.lean condition by condition in Fractions before any Lean is written.
usage: gen_blasius_w.py L h_den N digits w1_num w1_den out.json [FG FP FQ R as p/q strings]"""
import sys, json, math
from fractions import Fraction as Fr

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
def sqrt_up(x, D):  # rational s >= 0 with s^2 >= x, s a multiple of 1/D
    s = up(Fr(math.sqrt(float(x))) if x > 0 else Fr(0), D)
    while s * s < x: s += Fr(1, D)
    return s

def taylor(a, b, c, N, D):
    g, p, q = [a], [b], [c]
    for k in range(N):
        conv = sum(g[i] * q[k - i] for i in range(k + 1))
        g.append(rnd(p[k] / (k + 1), D)); p.append(rnd(q[k] / (k + 1), D)); q.append(rnd(-conv / 2 / (k + 1), D))
    return g, p, q

def defects(pg, pp, pq):
    return (qsub(qderiv(pg), pp), qsub(qderiv(pp), pq), qadd(qderiv(pq), qsmul(Fr(1, 2), qmul(pg, pq))))

def psd(mu, w1, w2, m, P3):
    m11, m12, m13, m22, m23, m33 = mu * w1, -w1 / 2, P3 / 4, mu * w2, -w2 / 2, mu + m / 2
    d2 = m11 * m22 - m12 ** 2
    d3 = m11 * (m22 * m33 - m23 ** 2) - m12 * (m12 * m33 - m23 * m13) + m13 * (m12 * m23 - m22 * m13)
    return m11 > 0 and d2 > 0 and d3 >= 0

def cellprop(T, c):
    t0, h, d, e, B, mu, w1, w2, r1 = (c[k] for k in ('t0', 'h', 'δ', 'ε', 'B', 'μ', 'w1', 'w2', 'r1'))
    pg, pp, pq = c['pg'], c['pp'], c['pq']
    d1, d2, d3 = defects(pg, pp, pq)
    E1, E2, E3 = qabs(d1, h), qabs(d2, h), qabs(d3, h)
    m = head(pg) - h * qabs(pg[1:], h) - r1
    ql, qh = head(pq) - h * qabs(pq[1:], h), head(pq) + h * qabs(pq[1:], h)
    conds = [0 <= t0, t0 + h <= T, 0 < h, 0 < w1, 0 < w2, 0 <= mu, mu * h < 1, 0 < d, 0 < e,
             w1 * E1 ** 2 + w2 * E2 ** 2 + E3 ** 2 < e ** 2, 0 <= r1, B ** 2 <= w1 * r1 ** 2,
             psd(mu, w1, w2, m, ql), psd(mu, w1, w2, m, qh), (d + e * h) / (1 - mu * h) <= B]
    return all(conds), conds

def min_mu(w1, w2, m, ql, qh, den=10000):
    lo, hi = Fr(0), Fr(1)
    while not (psd(hi, w1, w2, m, ql) and psd(hi, w1, w2, m, qh)): hi *= 2
    for _ in range(40):
        mid = (lo + hi) / 2
        if psd(mid, w1, w2, m, ql) and psd(mid, w1, w2, m, qh): hi = mid
        else: lo = mid
    return up(hi, den)

def main():
    L = Fr(sys.argv[1]); h = Fr(1, int(sys.argv[2])); N = int(sys.argv[3]); D = 10 ** int(sys.argv[4])
    w1 = Fr(int(sys.argv[5]), int(sys.argv[6])); w2 = Fr(1); out = sys.argv[7]
    RD = D * 1000  # resolution of radii
    cells = []
    a, b, c, delta = Fr(0), Fr(0), Fr(1), Fr(1, RD)
    t0 = Fr(0); amp_log = 0.0
    while t0 < L:
        pg, pp, pq = taylor(a, b, c, N, D)
        d1, d2, d3 = defects(pg, pp, pq)
        E1, E2, E3 = qabs(d1, h), qabs(d2, h), qabs(d3, h)
        eps = sqrt_up(w1 * E1 ** 2 + w2 * E2 ** 2 + E3 ** 2, RD) + Fr(1, RD)
        ql, qh = head(pq) - h * qabs(pq[1:], h), head(pq) + h * qabs(pq[1:], h)
        B = (delta + eps * h) * 2  # initial guess, then fixed point
        for _ in range(20):
            r1 = sqrt_up(B ** 2 / w1, RD)
            m = head(pg) - h * qabs(pg[1:], h) - r1
            mu = min_mu(w1, w2, m, ql, qh)
            assert mu * h < 1, (float(t0), float(mu))
            Bn = up((delta + eps * h) / (1 - mu * h), RD)
            if Bn <= B: B = Bn; break
            B = Bn
        r1 = sqrt_up(B ** 2 / w1, RD)
        m = head(pg) - h * qabs(pg[1:], h) - r1
        cell = {'t0': t0, 'h': h, 'δ': delta, 'ε': eps, 'B': B, 'μ': mu, 'w1': w1, 'w2': w2, 'r1': r1,
                'pg': pg, 'pp': pp, 'pq': pq}
        ok, conds = cellprop(L, cell)
        assert ok, (float(t0), [i for i, x in enumerate(conds) if not x])
        cells.append(cell); amp_log += float(mu * h)
        ea, eb, ec = qeval(pg, h), qeval(pp, h), qeval(pq, h)
        a, b, c = rnd(ea, D), rnd(eb, D), rnd(ec, D)
        s = sqrt_up(w1 * (ea - a) ** 2 + w2 * (eb - b) ** 2 + (ec - c) ** 2, RD)
        delta = B + s
        t0 += h
    last = cells[-1]
    eg, ep, eq = (qeval(last[k], last['h']) for k in ('pg', 'pp', 'pq'))
    B = last['B']; r1 = last['r1']; r2 = sqrt_up(B ** 2 / w2, RD)
    print('cells', len(cells), 'final B %.3g' % float(B), 'r1 %.3g' % float(r1), 'amp e^%.2f' % amp_log,
          'g', float(eg), 'p', float(ep), 'q', float(eq), 'max eps %.3g' % max(float(x['ε']) for x in cells))
    if len(sys.argv) > 8:
        FG, FP, FQ, R = (Fr(x) for x in sys.argv[8:12])
        ok = abs(eg - FG) + r1 <= R and abs(ep - FP) + r2 <= R and abs(eq - FQ) + B <= R
        print('end check against (FG, FP, FQ, R):', ok, float(abs(eg - FG) + r1), float(abs(ep - FP) + r2), float(abs(eq - FQ) + B))
    ser = lambda x: [x.numerator, x.denominator]
    json.dump({'L': ser(L), 'cells': [{k: ([ser(y) for y in v] if isinstance(v, list) else ser(v)) for k, v in cl.items()} for cl in cells],
               'end': [ser(eg), ser(ep), ser(eq)], 'r2': ser(r2)}, open(out, 'w'))

if __name__ == '__main__':
    main()
