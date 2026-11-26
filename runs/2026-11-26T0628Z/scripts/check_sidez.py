# Run 2026-11-26T0628Z: evaluate the side condition sideZ a X (Checked/FSRev/RZero.lean) on every cell of a
# tube JSON, exactly as Lean's decide will: (a <= t0+h -> 0 < qlo - B) and (t0 <= a <= t0+h -> ghi + r1 < 0)
# and (a <= t0+h -> glo - r1 <= 0 -> qhi + B < X).  usage: check_sidez.py cells.json a X
import json, sys
from fractions import Fraction as Fr
d = json.load(open(sys.argv[1])); a = Fr(sys.argv[2]); X = Fr(sys.argv[3])
fr = lambda v: Fr(v[0], v[1])
def qeval(p, x):
    r = Fr(0)
    for c in reversed(p): r = c + x * r
    return r
ok = True; worst = None
for i, c in enumerate(d['cells']):
    t0, h, B, r1 = fr(c['t0']), fr(c['h']), fr(c['B']), fr(c['r1'])
    pg = [fr(v) for v in c['pg']]; pq = [fr(v) for v in c['pq']]
    sg = h * qeval([abs(x) for x in pg[1:]], h); sq = h * qeval([abs(x) for x in pq[1:]], h)
    glo, ghi = pg[0] - sg, pg[0] + sg; qlo, qhi = pq[0] - sq, pq[0] + sq
    c1 = (not a <= t0 + h) or (0 < qlo - B)
    c2 = (not (t0 <= a <= t0 + h)) or (ghi + r1 < 0)
    c3 = (not a <= t0 + h) or (glo - r1 > 0) or (qhi + B < X)
    if a <= t0 + h and glo - r1 <= 0:
        m = X - (qhi + B)
        if worst is None or m < worst[0]: worst = (float(m), i, float(t0))
    if not (c1 and c2 and c3):
        ok = False; print('FAIL cell', i, float(t0), c1, c2, c3, float(qlo - B), float(ghi + r1), float(glo - r1), float(qhi + B))
print('OK' if ok else 'FAILED', 'tightest X margin (margin, cell, t0):', worst)
