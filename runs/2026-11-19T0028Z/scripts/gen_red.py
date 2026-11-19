"""Run 2026-11-19T0028Z: certificate generator for Checked/Trust/NecessityAV.lean.
Redundancy of the hypotheses Ωm ≤ 1 and 0 ≤ ΩΛ of Checked.Data.Moresco16Min.chiSqOL_ge: the χ² bound
14.9665 also holds on {Ωm ≥ 1, ΩΛ ≥ 0, E² ≥ 0} (region A) and {Ωm ≤ 1, ΩΛ ≤ 0, E² ≥ 0} (region B).
Each root box is covered by bisection; a leaf is
 - vac:  some E²(z_k) < 0 at all four corners (contradicts E² ≥ 0),
 - far:  some E²(z_a) ≥ q_a² at all four corners, with 63.712 q_a ≥ H_a + 3.87 σ_a (`far_hi`: for H₀ ≤ 63.712
         the prior term alone is ≥ 14.977; above it row a alone is),
 - box:  closed by Moresco16Min.box_boundQ (corner checks, kernel decide), as in run 2026-11-05T0628Z.
Outside each root box: one far row and a few rows of E² ≥ 0 make the half-plane piece infeasible (LP).
usage: python3 -I gen_red.py OUT.json"""
from fractions import Fraction as F
import math, json, sys
from scipy.optimize import linprog
T = [(0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
 (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
 (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9),
 (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
 (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
 (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]
T = [(F(str(z)), F(str(h)), F(str(s))) for z, h, s in T]
P = F(24, 10); w0 = 1 / P**2
gam = sum(h*h/s/s for z, h, s in T) + 73**2 / P**2
C = F('14.9665')
LO = F('63.712'); R = F('3.87')
assert (73 - LO)**2 / P**2 >= C and R**2 >= C
def y(z, m, l): return m*(1+z)**3 + (1-m-l)*(1+z)**2 + l
def alf(m, l): return sum(y(z, m, l)/s/s for z, h, s in T) + w0
def Lf(sv, m, l): return sum(h/s/s * (y(z, m, l) + si*si) / (2*si) for (z, h, s), si in zip(T, sv)) + 73 / P**2
Q = []
for z, h, s in T:
    q = F(math.ceil(float((h + R*s) / LO) * 1000), 1000)
    assert LO * q >= h + R*s
    Q.append(q)
def corners(b):
    m0, m1, l0, l1 = b
    return [(m0, l0), (m0, l1), (m1, l0), (m1, l1)]
def leaf(b):
    cs = corners(b)
    for k, (z, h, s) in enumerate(T):
        if all(y(z, m, l) < 0 for m, l in cs): return {'vac': k}
    for a, (z, h, s) in enumerate(T):
        if all(y(z, m, l) >= Q[a]**2 for m, l in cs): return {'far': a, 'q': str(Q[a])}
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
def coef(z): return (float((1+z)**2), float(z*(1+z)**2), float(-z*(2+z)))   # y = c + a m + b l
def outer(piece):
    """piece: list of (am, al, rhs) meaning am*m + al*l <= rhs. Find far row a and hy rows K
    (|K| <= 2) with the system infeasible (so linarith closes it)."""
    import itertools
    for a in range(30):
        ca, aa, ba = coef(T[a][0])
        far = ([aa, ba], float(Q[a]**2) - ca - 1e-9)     # y_a < q_a^2  (strictly, shrunk)
        for n in (0, 1, 2):
            for K in itertools.combinations(range(30), n):
                A = [[p[0], p[1]] for p in piece] + [far[0]]
                b = [float(p[2]) for p in piece] + [far[1]]
                for k in K:
                    c, am, bl = coef(T[k][0]); A.append([-am, -bl]); b.append(c)
                r = linprog([0, 0], A_ub=A, b_ub=b, bounds=[(None, None)]*2)
                if r.status == 2:
                    return {'far': a, 'q': str(Q[a]), 'hy': list(K)}
    raise SystemExit('outer piece not closed: ' + str(piece))
out = {'c': str(C)}
# Region A: m >= 1, l >= 0.  Root [1, 13/5] x [0, 17/4].
out['A'] = {'tree': build((F(1), F(13, 5), F(0), F(17, 4))),
            'out_m': outer([(-1, 0, -F(13, 5)), (0, -1, 0)]),            # m >= 13/5, l >= 0
            'out_l': outer([(-1, 0, -1), (1, 0, F(13, 5)), (0, -1, -F(17, 4))])}  # 1<=m<=13/5, l>=17/4
# Region B: m <= 1, l <= 0.  Root [-3/2, 1] x [-2, 0].
out['B'] = {'tree': build((F(-3, 2), F(1), F(-2), F(0))),
            'out_m': outer([(1, 0, -F(3, 2)), (0, 1, 0)]),               # m <= -3/2, l <= 0
            'out_l': outer([(-1, 0, F(3, 2)), (1, 0, 1), (0, 1, -2)])}   # -3/2<=m<=1, l<=-2
def count(t):
    if 'split' in t: a = count(t['lo']); b = count(t['hi']); return tuple(x+y for x, y in zip(a, b))
    return (1, 0, 0) if 'vac' in t else (0, 1, 0) if 'far' in t else (0, 0, 1)
for k in 'AB':
    print(k, 'vac/far/box leaves:', count(out[k]['tree']), 'outer:', out[k]['out_m'], out[k]['out_l'], file=sys.stderr)
json.dump(out, open(sys.argv[1], 'w'))
