"""Referee (run 2026-11-05T0628Z): are the hypotheses of chiSqOL_ge needed?
(a) keep only 'E^2 >= 0 at all 30 z_i' (drop m <= 1 and l >= 0): branch and bound over large boxes.
(b) drop every hypothesis and use Lean's junk Real.sqrt (sqrt of a negative = 0): branch and bound with
    the natural enclosure (clipped y), centred form only where all y_i > 0 on the box.
Run: python3 -I referee_min_hyp.py
"""
import math, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import referee_min as R

def lower_junk(box):
    m0, m1, l0, l1 = box
    ylo, yhi = [], []
    for A, Bm, Bl, wh, w in R.COEF:
        c = [A + m*Bm + l*Bl for m in (m0, m1) for l in (l0, l1)]
        ylo.append(max(min(c), 0.0)); yhi.append(max(max(c), 0.0))
    if all(v > 1e-12 for v in ylo):
        return R.lower(box)
    alo = R.W0 + sum(w*lo for (A, Bm, Bl, wh, w), lo in zip(R.COEF, ylo))
    bhi = R.W0*73 + sum(wh*math.sqrt(hi) for (A, Bm, Bl, wh, w), hi in zip(R.COEF, yhi))
    return R.GAMMA - bhi*bhi/alo

def bnb(region, target, low, maxboxes=6_000_000, minw=1e-9):
    todo = [region]; n = 0; fail = []
    while todo:
        b = todo.pop(); n += 1
        if n > maxboxes: fail.append(b); break
        lb = low(b)
        if lb is None or lb - R.SAFETY >= target: continue
        if b[1]-b[0] < minw and b[3]-b[2] < minw: fail.append(b); continue
        m0, m1, l0, l1 = b
        if (m1-m0) >= (l1-l0):
            mm = (m0+m1)/2; todo += [(m0, mm, l0, l1), (mm, m1, l0, l1)]
        else:
            lm = (l0+l1)/2; todo += [(m0, m1, l0, lm), (m0, m1, lm, l1)]
    return n, len(fail), fail[:3]

for S in (5, 50, 1000):
    print(f"(a) E^2>=0 only, box [-{S},{S}]^2:", bnb((-S, S, -S, S), 14.9665, R.lower))
for S in (5, 50, 1000):
    print(f"(b) Lean junk sqrt, no hypotheses, box [-{S},{S}]^2:", bnb((-S, S, -S, S), 14.9665, lower_junk))
