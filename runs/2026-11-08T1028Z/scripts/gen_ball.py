#!/usr/bin/env python3
"""Run 2026-11-08T1028Z: Hiemenz shooting events for a whole BALL of wall values.
Same cells as runs/2026-11-07T2028Z/scripts/gen_hiemenz_w.py, but the first cell's input radius is
r (every solution with |q(0) - A| <= r starts in the first cell's ball, since g(0) = p(0) = 0 exactly),
and the chain stops at the first cell end where the event holds (mode 'under': q + B < 0 at the end;
mode 'over': p - r2 > 1 at the end), never beyond L.
API: run(A, r, L, hden, N, digits, w1, w2, mode) -> (ok, cells, info)."""
import sys, json, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '2026-11-07T2028Z', 'scripts'))
from gen_hiemenz_w import taylor, defects, qabs, qeval, sqrt_up, up, rnd, corners, min_mu, cellprop, rng
from fractions import Fraction as Fr

def run(A, r, L, hden, N, digits, w1, w2, mode, maxcells=400):
    h = Fr(1, hden); D = 10 ** digits; RD = D * 1000
    cells = []; a, b, c, delta = Fr(0), Fr(0), A, r
    t0 = Fr(0)
    while t0 < L and len(cells) < maxcells:
        pg, pp, pq = taylor(a, b, c, N, D)
        d1, d2, d3 = defects(pg, pp, pq)
        E1, E2, E3 = qabs(d1, h), qabs(d2, h), qabs(d3, h)
        eps = sqrt_up(w1 * E1 ** 2 + w2 * E2 ** 2 + E3 ** 2, RD) + Fr(1, RD)
        B = (delta + eps * h) * 2
        cell = {'t0': t0, 'h': h, 'δ': delta, 'ε': eps, 'w1': w1, 'w2': w2, 'pg': pg, 'pp': pp, 'pq': pq}
        okB = False
        for _ in range(30):
            cell['B'] = B; cell['r1'] = sqrt_up(B ** 2 / w1, RD); cell['r2'] = sqrt_up(B ** 2 / w2, RD)
            m, cs = corners(cell)
            mu = min_mu(w1, w2, m, cs)
            if mu * h >= 1: return False, cells, 'mu*h>=1 at %g' % float(t0)
            Bn = up((delta + eps * h) / (1 - mu * h), RD)
            if Bn <= B: B = Bn; okB = True; break
            B = Bn
        if not okB: return False, cells, 'B no fixpoint'
        cell['B'] = B; cell['r1'] = sqrt_up(B ** 2 / w1, RD); cell['r2'] = sqrt_up(B ** 2 / w2, RD)
        m, cs = corners(cell); cell['μ'] = min_mu(w1, w2, m, cs)
        ok, conds = cellprop(L, cell)
        if not ok: return False, cells, 'cellprop'
        if mode == 'under':
            if not (rng(pp, h)[1] + cell['r2'] < 1): return False, cells, 'side p<1 fails at %g' % float(t0)
        else:
            if not (rng(pq, h)[0] - B > 0): return False, cells, 'side q>0 fails at %g' % float(t0)
        cells.append(cell)
        eg, ep, eq = qeval(pg, h), qeval(pp, h), qeval(pq, h)
        if mode == 'under' and eq + B < 0: return True, cells, 'event at %s' % (t0 + h)
        if mode == 'over' and ep - cell['r2'] > 1: return True, cells, 'event at %s' % (t0 + h)
        a, b, c = rnd(eg, D), rnd(ep, D), rnd(eq, D)
        s = sqrt_up(w1 * (eg - a) ** 2 + w2 * (eb - b) ** 2 + (eq - c) ** 2, RD) if False else \
            sqrt_up(w1 * (eg - a) ** 2 + w2 * (ep - b) ** 2 + (eq - c) ** 2, RD)
        delta = B + s
        t0 += h
    return False, cells, 'no event by L'
