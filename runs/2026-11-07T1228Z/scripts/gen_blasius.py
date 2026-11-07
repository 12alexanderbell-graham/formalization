#!/usr/bin/env python3
"""Exact-rational validated cells for the Blasius IVP g''' + g g''/2 = 0, g(0)=g'(0)=0, g''(0)=1 on [0, L]
(run 2026-11-07T1228Z). Mirrors the Lean `CellProp` of Work/Blasius/BCellQ.lean condition by condition, in
Fractions, before any Lean is written. Writes cells to a JSON file.
usage: gen_blasius.py L_num L_den h_den N digits out.json"""
import sys, json
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

def rnd(x, D):  # round to nearest multiple of 1/D
    return Fr(round(x * D), D)

def taylor(a, b, c, N, D):
    g, p, q = [a], [b], [c]
    for k in range(N):
        conv = sum(g[i] * q[k - i] for i in range(k + 1))
        g.append(rnd(p[k] / (k + 1), D)); p.append(rnd(q[k] / (k + 1), D)); q.append(rnd(-conv / 2 / (k + 1), D))
    return g, p, q

def defects(c):
    d1 = qsub(qderiv(c['pg']), c['pp'])
    d2 = qsub(qderiv(c['pp']), c['pq'])
    d3 = qadd(qderiv(c['pq']), qsmul(Fr(1, 2), qmul(c['pg'], c['pq'])))
    return d1, d2, d3

def cellprop(T, c):
    t0, h, d, e, B, GH, QH, K = (c[k] for k in ('t0', 'h', 'δ', 'ε', 'B', 'GH', 'QH', 'K'))
    pg, pq = c['pg'], c['pq']
    d1, d2, d3 = defects(c)
    conds = [0 <= t0, t0 + h <= T, 0 < h, 1 <= K, (GH + QH) / 2 <= K, K * h < 1, 0 <= d, 0 <= e,
             -(GH - Fr(1, 100)) <= head(pg) - h * qabs(pg[1:], h), head(pg) + h * qabs(pg[1:], h) <= GH - Fr(1, 100),
             -(QH - Fr(1, 100)) <= head(pq) - h * qabs(pq[1:], h), head(pq) + h * qabs(pq[1:], h) <= QH - Fr(1, 100),
             qabs(d1, h) <= e, qabs(d2, h) <= e, qabs(d3, h) <= e,
             d * (1 / (1 - K * h)) + e / K * (1 / (1 - K * h) - 1) <= B, B < Fr(1, 100)]
    return all(conds), conds

def up(x, D):  # round up to a multiple of 1/D (positive x)
    n = x * D
    return Fr(-((-n.numerator) // n.denominator), D)

def main():
    L = Fr(int(sys.argv[1]), int(sys.argv[2])); h = Fr(1, int(sys.argv[3])); N = int(sys.argv[4]); D = 10 ** int(sys.argv[5])
    out = sys.argv[6]
    cells = []
    a, b, c, delta = Fr(0), Fr(0), Fr(1), Fr(0)
    t0 = Fr(0)
    while t0 < L:
        pg, pp, pq = taylor(a, b, c, N, D)
        cell = {'t0': t0, 'h': h, 'δ': delta, 'pg': pg, 'pp': pp, 'pq': pq}
        d1, d2, d3 = defects(cell)
        eps = up(max(qabs(d1, h), qabs(d2, h), qabs(d3, h)) * Fr(11, 10) + Fr(1, 10 ** 40), 10 ** 40)
        GH = up(max(abs(head(pg)) + h * qabs(pg[1:], h), Fr(0)) + Fr(2, 100), 1000)
        QH = up(abs(head(pq)) + h * qabs(pq[1:], h) + Fr(2, 100), 1000)
        K = max(Fr(1), (GH + QH) / 2)
        Bx = delta * (1 / (1 - K * h)) + eps / K * (1 / (1 - K * h) - 1)
        B = up(Bx * (1 + Fr(1, 10 ** 6)) + Fr(1, 10 ** 40), 10 ** 40)
        cell.update({'ε': eps, 'B': B, 'GH': GH, 'QH': QH, 'K': K})
        ok, conds = cellprop(L, cell)
        assert ok, (float(t0), [i for i, x in enumerate(conds) if not x])
        cells.append(cell)
        # next cell start: rounded end values, input radius
        ea, eb, ec = qeval(pg, h), qeval(pp, h), qeval(pq, h)
        a, b, c = rnd(ea, D), rnd(eb, D), rnd(ec, D)
        delta = up(max(abs(ea - a), abs(eb - b), abs(ec - c)) + B, 10 ** 40)
        t0 += h
    last = cells[-1]
    eg, ep, eq = (qeval(last[k], last['h']) for k in ('pg', 'pp', 'pq'))
    print('cells', len(cells), 'final B', float(last['B']), 'g', float(eg), 'p', float(ep), 'q', float(eq))
    ser = lambda x: [x.numerator, x.denominator]
    json.dump({'L': ser(L), 'cells': [{k: ([ser(y) for y in v] if isinstance(v, list) else ser(v)) for k, v in cl.items()} for cl in cells],
               'end': [ser(eg), ser(ep), ser(eq)]}, open(out, 'w'))

if __name__ == '__main__':
    main()
