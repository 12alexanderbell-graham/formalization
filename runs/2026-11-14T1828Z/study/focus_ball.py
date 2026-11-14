"""Float study (unchecked; run 2026-11-14T1828Z) for STATE 0u's infinite-horizon step: on a box
[1-r, 1+r] x [2-r, 2+r] around the focus, the best one-sided constant mu of the homology field in the
weighted norm of BEOCell (corner test copied from gen_bo.py), and the angular velocity in the Jordan basis."""
from fractions import Fraction as F
import math
def corner_ok(m1, m2, mu):
    a = 16 * m1 + 6 * m2 + 8 * mu - 24; b = 10 * m1 - 2 * m2 + 4 * mu - 4; c = -2 * m1 + 4 * mu + 4
    return a > 0 and b * b <= 4 * a * c
def best_mu(UL, UH, VL, VH):
    lo_, hi_ = -1.0, 0.0
    if not all(corner_ok(m1, m2, hi_) for m1 in (UL, UH) for m2 in (VL, VH)): return None
    for _ in range(40):
        mid = (lo_ + hi_) / 2
        if all(corner_ok(m1, m2, mid) for m1 in (UL, UH) for m2 in (VL, VH)): hi_ = mid
        else: lo_ = mid
    return hi_
for r in [0.001, 0.003, 0.01, 0.03, 0.05, 0.1, 0.2]:
    print('r', r, 'mu', best_mu(1 - r, 1 + r, 2 - r, 2 + r))
# angular velocity: Jordan coordinates a = sqrt7 e1, b = e1 + 2 e2 (N = a^2 + b^2); field f(e) at focus+e
def field(u, v): return (u * (3 - u - v), v * (u - 1))
worst = {}
for r in [0.003, 0.01, 0.03, 0.05]:
    wmin = 1e9
    for k in range(3600):
        th = 2 * math.pi * k / 3600
        a, b = r * math.cos(th), r * math.sin(th)
        e1 = a / math.sqrt(7); e2 = (b - e1) / 2
        f1, f2 = field(1 + e1, 2 + e2)
        da = math.sqrt(7) * f1; db = f1 + 2 * f2
        w = (a * db - b * da) / (a * a + b * b)
        wmin = min(wmin, abs(w)) if True else wmin
        worst.setdefault(r, []).append(w)
    ws = worst[r]
    print('r', r, 'angular velocity min/max', min(ws), max(ws))
