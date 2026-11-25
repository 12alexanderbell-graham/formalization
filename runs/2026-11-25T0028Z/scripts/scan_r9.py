"""Witness of rl19_box_unmatched 9 (the expansion law dropped), run 2026-11-25T0028Z.

Float scan: scale factors whose Hubble rate is a power of 1 + z with one break (E = x^q1 up to x = Zj, then
continuous with exponent q2), distance d = Z * chi(Z); best spread (mag) of d/P over the three sources for a cubic
in the RL19 box. Flat LCDM (any density up to 20) and single power laws never get below 0.19 mag; q1 = 1
(coasting, a = t), q2 = 2 (a square root of t), Zj = 9/5 gives 0.044 mag. Then the exact-rational check of the
Lean numbers of Checked/Trust/NecessityBR.lean.
"""
import math
from fractions import Fraction as F

lam = math.log10(2)
Zs = {1: 2 ** .5, 3: 2 * 2 ** .5, 5: 4 * 2 ** .5}
P = lambda k, a2, a3: k * lam / 2 + a2 * (k * lam / 2) ** 2 + a3 * (k * lam / 2) ** 3


def chi(Z, q1, q2, Zj):
    f = lambda x0, x1, q, c: c * ((x1 ** (1 - q) - x0 ** (1 - q)) / (1 - q) if abs(q - 1) > 1e-9 else math.log(x1 / x0))
    if Z <= Zj:
        return f(1, Z, q1, 1)
    return f(1, Zj, q1, 1) + f(Zj, Z, q2, Zj ** (q2 - q1))


def spread(q1, q2, Zj):
    r = {k: Zs[k] * chi(Zs[k], q1, q2, Zj) for k in Zs}
    best = None
    for a2 in [3.43 + i * 0.01 for i in range(7)]:
        for a3 in [1.57 + i * 0.01 for i in range(13)]:
            q = [r[k] / P(k, a2, a3) for k in (1, 3, 5)]
            s = 5 * math.log10(max(q) / min(q))
            if best is None or s < best[0]:
                best = (s, a2, a3)
    return best


print('coasting + square root, break 9/5:', spread(1, 2, 1.8))
print('single power law q = 3/2 (Einstein-de Sitter):', spread(1.5, 1.5, 2))

# exact rationals: d bounds from sqrt2 in [1.41421, 1.41422], log 2 (Mathlib d9), log(9/10) by six series terms
x = F(1, 10)
S = sum(x ** (i + 1) / (i + 1) for i in range(6))
err = x ** 7 / (1 - x)
l2lo, l2hi = F(6931471803, 10 ** 10), F(6931471808, 10 ** 10)
L95 = (l2lo - S - err, l2hi - S + err)
assert F('0.58778656') <= L95[0] and L95[1] <= F('0.5877868')
s2 = (F('1.41421'), F('1.41422'))
d = {1: (s2[0] * l2lo / 2, s2[1] * l2hi / 2),
     3: (2 * s2[0] * (1 + F('0.58778656')) - F(9, 5), 2 * s2[1] * (1 + F('0.5877868')) - F(9, 5)),
     5: (4 * s2[0] * (1 + F('0.58778656')) - F(9, 5), 4 * s2[1] * (1 + F('0.5877868')) - F(9, 5))}
dl = {1: F('0.490127'), 3: F('2.690927'), 5: F('7.181854')}
du = {1: F('0.490132'), 3: F('2.69096'), 5: F('7.18192')}
lam_lo, lam_hi = F('0.30101'), F('0.30105')
a2, a3 = F(87, 25), F(169, 100)
Bc = lambda t: t + a2 * t ** 2 + a3 * t ** 3
Bl = {1: F('0.235094'), 3: F('1.316529'), 5: F('3.443421')}
Bu = {1: F('0.235138'), 3: F('1.316841'), 5: F('3.444333')}
Ll, Lu, H = F('2.30249'), F('2.30268'), F('1.1153')
for k in (1, 3, 5):
    assert dl[k] <= d[k][0] and d[k][1] <= du[k], k
    assert Bl[k] <= Bc(F(k, 2) * lam_lo) and Bc(F(k, 2) * lam_hi) <= Bu[k], k
    assert F(98, 100) * (Lu / H * Bu[k]) <= dl[k] and du[k] <= F(102, 100) * (Ll / H * Bl[k]), k
print('all exact checks pass')
