"""Certified step bounds of J_Z = int_{1/sqrt Z}^1 2/sqrt(100 - 99 v^6) dv at Omega = 100 (run 2026-11-18T0628Z).
Emits Lean `have` lines; Lean (norm_num) checks every inequality. Exact rationals only."""
from fractions import Fraction as F
import math
Om = F(100)
R = lambda v: Om + (1 - Om) * v**6
def gl(p):   # c with R(p) <= (2/c)^2, c close to g(p) from below
    c = F(math.floor(2 / math.sqrt(R(p)) * 10**6), 10**6)
    while R(p) > (2 / c)**2: c -= F(1, 10**6)
    return c
def gu(q):   # c with (2/c)^2 <= R(q), c close to g(q) from above
    c = F(math.ceil(2 / math.sqrt(R(q)) * 10**6), 10**6)
    while (2 / c)**2 > R(q): c += F(1, 10**6)
    return c
n = 20
a = F('0.5947')
pts = sorted(set([a] + [F(round(float(1 - (1 - a) * (1 - F(i, n))**2), 4)).limit_denominator(10**4) for i in range(1, n)] + [F(1)]))
lo = sum((pts[i+1] - pts[i]) * gl(pts[i]) for i in range(len(pts) - 1))
kp = [F('0.4204'), F('0.46'), F('0.50'), F('0.54'), F('0.5947')]
up = sum((kp[i+1] - kp[i]) * gu(kp[i+1]) for i in range(len(kp) - 1))
Rr = F('1.318')
print('-- J3 >=', float(lo), ' K <=', float(up), ' ratio bound', float((lo + up) / lo), 'ok', up <= (Rr - 1) * lo)
def d(x): return f'({x.numerator} / {x.denominator} : ℝ)'
L = []
for i in range(len(pts) - 1):
    p, q = pts[i], pts[i+1]
    L.append(f'  have P{i} := piece_lo 100 {d(p)} {d(q)} {d(gl(p))} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)')
for i in range(len(pts) - 2):
    L.append(f'  have S{i} := int_split 100 {d(pts[i])} {d(pts[i+1])} (by norm_num) (by norm_num) (by norm_num) (by norm_num)')
for i in range(len(kp) - 1):
    p, q = kp[i], kp[i+1]
    L.append(f'  have U{i} := piece_up 100 {d(p)} {d(q)} {d(gu(q))} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)')
for i in range(len(kp) - 1):
    L.append(f'  have T{i} := int_split 100 {d(kp[i])} {d(kp[i+1])} (by norm_num) (by norm_num) (by norm_num) (by norm_num)')
print('\n'.join(L))
print('-- npts', len(pts), [float(x) for x in pts])
