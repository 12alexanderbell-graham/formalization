"""Numbers of Checked/Trust/NecessityBQ.lean (run 2026-11-25T0028Z), exact rationals.

1. Witness of third_coefficient_lower_bound 17 and 10: the Einstein-de Sitter model of NCAR (distance
   3 Z (1 - sqrt(1/Z)) with H0 = 2/3), the cubic a2 = 50, a3 = 13/5, normalisation H = 7.175, offset 0.
   Bc(a2, a3, k lam / 2) is increasing in lam for these coefficients, so its range over
   lam in [0.30101, 0.30105] (NCAQ.lam_bd) is [Bc(k lo/2), Bc(k hi/2)], rounded outward to 1e-6.
   resid_band needs 0.98 (Lu/H) Bu <= dl and du <= 1.02 (Ll/H) Bl with NCAQ.log10_bd and NCAR.d3_bd/d5_bd.
2. Why a3 <= 13/5 needs a large a2 when the nearest source is dropped (float scan, printed).
3. rl19_box_unmatched 10: the box ratio Bc(5u)/Bc(3u) <= 2.65 and the integral ratio
   J5/J3 >= (1 - w5)/(1 - w3) contradict the two residuals (kappa = 0.95499).
"""
from fractions import Fraction as F
import math

a2, a3 = F(50), F(13, 5)
lo, hi = F('0.30101'), F('0.30105')
Bc = lambda a2, a3, x: x + a2 * x ** 2 + a3 * x ** 3
Ll, Lu = F('2.30249'), F('2.30268')
d = {3: (F('3.439075'), F('3.439949')), 5: (F('9.834416'), F('9.836183'))}
H = F('7.175')
for k in (1, 3, 5):
    bl, bu = Bc(a2, a3, F(k, 2) * lo), Bc(a2, a3, F(k, 2) * hi)
    bl6, bu6 = F(math.floor(bl * 10 ** 6), 10 ** 6), F(math.ceil(bu * 10 ** 6), 10 ** 6)
    print('k', k, 'B in', float(bl6), float(bu6))
    if k > 1:
        c1 = F(98, 100) * (Lu / H * bu6) <= d[k][0]
        c2 = d[k][1] <= F(102, 100) * (Ll / H * bl6)
        print('   resid_band conditions', c1, c2)
        assert c1 and c2

# 2. float scan: spread (mag) of d/P at the two farther sources, a3 = 13/5
lam = math.log(2) / math.log(10)
dE = lambda Z: 3 * Z * (1 - math.sqrt(1 / Z))
for A2 in (5, 20, 50, 200):
    q3 = dE(2 * 2 ** .5) / Bc(A2, 2.6, 1.5 * lam)
    q5 = dE(4 * 2 ** .5) / Bc(A2, 2.6, 2.5 * lam)
    print('a2', A2, 'spread mag', abs(5 * math.log10(q5 / q3)))

# 3. RL19 box, nearest source dropped
u = hi / 2
worst = -F(1475, 1000) + F(2875, 10000) * F(349, 100) * hi + F(668125, 100000) * F(169, 100) * hi ** 2
print('box: Bc(5u) - 2.65 Bc(3u) <= lam *', float(worst))
assert worst < 0
lhs = F(95499, 100000) * 4 * F(5795, 10000)   # times J3, from J5 >= (5795/4054) J3
rhs = 2 * F(265, 100) * F(4054, 10000)
print('contradiction margin', float(lhs - rhs))
assert lhs > rhs
