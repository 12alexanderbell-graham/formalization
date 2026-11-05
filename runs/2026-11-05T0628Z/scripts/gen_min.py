"""Exact-rational certificate generator for Work/Data/Moresco16MinCerts*.lean (run 2026-11-05T0628Z).
Covers (Om, OL) in [-1, 1] x [0, 4] by adaptive bisection. Each leaf box is either
 - vacuous: some E^2(z_i) (affine in Om, OL) is < 0 at all four corners, or
 - closed: with s_i = sqrt(E^2_i(centre)) rounded to 5 decimals (>= 1/10^3),
   Lf(s; corner)^2 <= alf(corner) * (gam - c) at all four corners, checked in exact arithmetic.
Output: JSON tree; emit_min.py writes the Lean."""
from fractions import Fraction as F
import math, json, sys
T = [(0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
 (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
 (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9),
 (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
 (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
 (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]
T = [(F(str(z)), F(str(h)), F(str(s))) for z, h, s in T]
P = F(24, 10)
w0 = 1 / P**2
gam = sum(h*h/s/s for z, h, s in T) + 73**2 / P**2
def y(z, m, l): return m*(1+z)**3 + (1-m-l)*(1+z)**2 + l
def alf(m, l): return sum(y(z, m, l)/s/s for z, h, s in T) + w0
def Lf(sv, m, l): return sum(h/s/s * (y(z, m, l) + si*si) / (2*si) for (z, h, s), si in zip(T, sv)) + 73 / P**2
C = F(sys.argv[1]) if len(sys.argv) > 1 else F('14.9665')
def corners(b):
    m0, m1, l0, l1 = b
    return [(m0, l0), (m0, l1), (m1, l0), (m1, l1)]
def leaf(b):
    cs = corners(b)
    for k, (z, h, s) in enumerate(T):
        if all(y(z, m, l) < 0 for m, l in cs): return {'vac': k}
    mc, lc = (b[0]+b[1])/2, (b[2]+b[3])/2
    sv = []
    for z, h, s in T:
        v = max(float(y(z, mc, lc)), 1e-6)
        sv.append(max(F(round(math.sqrt(v) * 10**5)), F(100)) / 10**5)
    if all(Lf(sv, m, l)**2 <= alf(m, l) * (gam - C) for m, l in cs):
        return {'s': [str(x) for x in sv]}
    return None
def build(b, depth=0):
    r = leaf(b)
    if r is not None:
        r['box'] = [str(x) for x in b]; return r
    if depth > 40: raise SystemExit('fail at ' + str(b))
    m0, m1, l0, l1 = b
    if m1 - m0 >= (l1 - l0) / 2:
        mid = (m0 + m1) / 2; return {'split': 'm', 'at': str(mid), 'box': [str(x) for x in b],
            'lo': build((m0, mid, l0, l1), depth+1), 'hi': build((mid, m1, l0, l1), depth+1)}
    mid = (l0 + l1) / 2; return {'split': 'l', 'at': str(mid), 'box': [str(x) for x in b],
        'lo': build((m0, m1, l0, mid), depth+1), 'hi': build((m0, m1, mid, l1), depth+1)}
tree = build((F(-1), F(1), F(0), F(4)))
def count(t):
    if 'split' in t: a = count(t['lo']); b = count(t['hi']); return tuple(x+y for x, y in zip(a, b))
    return (1, 0) if 'vac' in t else (0, 1)
print('vacuous, closed:', count(tree), file=sys.stderr)
json.dump({'c': str(C), 'tree': tree}, open(sys.argv[2] if len(sys.argv) > 2 else 'tree.json', 'w'))
