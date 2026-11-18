# Exact-rational generator (kept): fit_direction without Omega <= 1, flat model of negative cosmological
# constant (NCAQ.sa) at Omega = O; integrand 2/sqrt(O + (1-O) v^6) increasing in v.
from fractions import Fraction as F
import math, sys
O = F(3, 2)
a2, a3 = F(2, 5), F(31, 10)
lam = (F(30101, 100000), F(30105, 100000)); L = (F(230249, 100000), F(230268, 100000))
s2 = (F(141421, 100000), F(141422, 100000))
W = {1: (F(8408, 10000), F(8409, 10000)), 3: (F(5946, 10000), F(5947, 10000)), 5: (F(4204, 10000), F(4205, 10000))}
Zk = {1: F(1, 2), 3: F(3, 2), 5: F(5, 2)}   # x = k lam
def y(v): return O + (1 - O) * v**6
def rd(x, d=10000): return F(math.floor(x * d), d)
def ru(x, d=10000): return F(math.ceil(x * d), d)
def grid(start, n):
    # points refined toward 1 (steep end): p_i = 1 - (1-start) (1 - i/n)^2 ... use uniform in sqrt
    pts = [start] + [ru(1 - (1 - start) * (1 - F(i, n))**2) for i in range(1, n)] + [F(1)]
    return pts
def lower(start, n):
    pts = grid(start, n); cs = []
    for p, q in zip(pts, pts[1:]):
        c = rd(2 / math.sqrt(float(y(p)))); assert y(p) <= (2 / c)**2; cs.append(c)
    return pts, cs, sum((q - p) * c for p, q, c in zip(pts, pts[1:], cs))
def upper(start, n):
    pts = grid(start, n); cs = []
    for p, q in zip(pts, pts[1:]):
        c = ru(2 / math.sqrt(float(y(q)))); assert (2 / c)**2 <= y(q); cs.append(c)
    return pts, cs, sum((q - p) * c for p, q, c in zip(pts, pts[1:], cs))
def B(x): return x + a2 * x**2 + a3 * x**3
n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
res = {}
for i in (1, 3, 5):
    lo = lower(W[i][1], n); up = upper(W[i][0], n)
    Z = {1: (s2[0], s2[1]), 3: (2 * s2[0], 2 * s2[1]), 5: (4 * s2[0], 4 * s2[1])}[i]
    d = (Z[0] * lo[2], Z[1] * up[2])
    Bb = (B(Zk[i] * lam[0]), B(Zk[i] * lam[1]))
    Bb = (rd(Bb[0], 10**6), ru(Bb[1], 10**6))
    res[i] = (lo, up, d, Bb)
Hlo = max(F(98, 100) * L[1] * res[i][3][1] / res[i][2][0] for i in res)
Hhi = min(F(102, 100) * L[0] * res[i][3][0] / res[i][2][1] for i in res)
print('n', n, 'H window', float(Hlo), float(Hhi), 'ok' if Hlo < Hhi else 'EMPTY')
for i in res: print(' ', i, 'J', float(res[i][0][2]), float(res[i][1][2]), 'B', res[i][3])
# violation: a2 - L(3/2 - 3/4 O) + 1/2 >= 20/3 lam (a3 - L^2 (9/8 O^2 - 2 O + 7/6))
c2 = F(3, 2) - F(3, 4) * O; c3 = F(9, 8) * O**2 - 2 * O + F(7, 6)
lhs_min = min(a2 - l * c2 + F(1, 2) for l in L)
rhs_max = max(F(20, 3) * m * (a3 - l * l * c3) for m in lam for l in L)
print('violation margin', float(lhs_min - rhs_max), 'c2', c2, 'c3', c3)
if Hlo < Hhi: print('H', ru(Hlo))
