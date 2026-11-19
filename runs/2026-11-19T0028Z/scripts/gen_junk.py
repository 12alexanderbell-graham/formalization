"""Run 2026-11-19T0028Z: certificates for the third hypothesis (squared factor nonnegative at every row)
of Checked.Data.Moresco16Min.chiSqOL_ge: the bound 14.9665 on {Ωm ≤ 1, ΩΛ ≥ 0} with no sign condition
(Lean's √ of a negative number is 0). Root box [-3/5, 1] x [0, 13/4]; outside it row 28 (z = 1.75) has a
squared factor ≤ 0 and its term alone is ≥ 25. Leaves:
 - hy:   every squared factor ≥ 0 at the four corners → Moresco16Min.chiSqOL_ge itself,
 - neg:  a row k with H_k²/σ_k² ≥ 14.9665 has squared factor ≤ 0 at all four corners (`neg_row`),
 - far:  as in gen_red.py (`far_hi`),
 - jbox: corner certificate with every squared factor ≥ −s_i² (`box_boundQJ`).
usage: python3 -I gen_junk.py OUT.json"""
from fractions import Fraction as F
import math, json, sys, os
sys.argv_saved = sys.argv; out_path = sys.argv[1]
T = [(0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
 (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
 (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9),
 (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
 (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
 (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]
T = [(F(str(z)), F(str(h)), F(str(s))) for z, h, s in T]
P = F(24, 10); w0 = 1 / P**2
gam = sum(h*h/s/s for z, h, s in T) + 73**2 / P**2
C = F('14.9665'); LO = F('63.712'); R = F('3.87')
assert C < gam
def y(z, m, l): return m*(1+z)**3 + (1-m-l)*(1+z)**2 + l
def alf(m, l): return sum(y(z, m, l)/s/s for z, h, s in T) + w0
def Lf(sv, m, l): return sum(h/s/s * (y(z, m, l) + si*si) / (2*si) for (z, h, s), si in zip(T, sv)) + 73 / P**2
Q = [F(math.ceil(float((h + R*s) / LO) * 1000), 1000) for z, h, s in T]
STRONG = [k for k, (z, h, s) in enumerate(T) if h*h/s/s >= C]
def corners(b):
    m0, m1, l0, l1 = b
    return [(m0, l0), (m0, l1), (m1, l0), (m1, l1)]
def leaf(b):
    cs = corners(b)
    if all(y(z, m, l) >= 0 for z, h, s in T for m, l in cs): return {'hy': 1}
    for k in STRONG:
        if all(y(T[k][0], m, l) <= 0 for m, l in cs): return {'neg': k}
    for a, (z, h, s) in enumerate(T):
        if all(y(z, m, l) >= Q[a]**2 for m, l in cs): return {'far': a, 'q': str(Q[a])}
    mc, lc = (b[0]+b[1])/2, (b[2]+b[3])/2
    sv = []
    for z, h, s in T:
        lo = min(y(z, m, l) for m, l in cs)
        v = max(float(y(z, mc, lc)), 1e-6)
        si = max(F(round(math.sqrt(v) * 10**5)), F(100)) / 10**5
        if lo + si*si < 0:
            si = F(math.ceil(math.sqrt(float(-lo)) * 10**5) + 1, 10**5)
        sv.append(si)
    if all(y(z, m, l) + si*si >= 0 for (z, h, s), si in zip(T, sv) for m, l in cs) and \
       all(Lf(sv, m, l)**2 <= alf(m, l) * (gam - C) for m, l in cs):
        return {'s': [str(x) for x in sv], 'j': 1}
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
# outside the root box: row 28
z28 = T[28][0]
assert y(z28, F(-3, 5), F(0)) < 0 and 7.5625 + 1.75*7.5625*1 - 1.75*3.75*3.25 < 0
tree = build((F(-3, 5), F(1), F(0), F(13, 4)))
def count(t, key):
    if 'split' in t: return count(t['lo'], key) + count(t['hi'], key)
    return 1 if key in t else 0
print({k: count(tree, k) for k in ('hy', 'neg', 'far', 'j')}, 'strong', STRONG, file=sys.stderr)
json.dump({'c': str(C), 'C': {'tree': tree}}, open(out_path, 'w'))
