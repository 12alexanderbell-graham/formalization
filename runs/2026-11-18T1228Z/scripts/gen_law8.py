# Exact-rational generator (kept): Einstein-de Sitter witnesses for the law hypothesis (8) of
# B1Sep.cubic_separation and B1Sep.cubic_direction (Omega parameter 1/5, model density one).
# Distances at z = 3, 7 (H0 = 2/3, a0 = 1): d3 = 6, d7 = 24 (1 - sqrt(1/8)).
from fractions import Fraction as F
import math
lam = (F(30101, 100000), F(30105, 100000)); L = (F(230249, 100000), F(230268, 100000))
s8 = (F(353553, 1000000), F(353554, 1000000))      # sqrt(1/8)
d3 = (F(6), F(6)); d7 = (24 * (1 - s8[1]), 24 * (1 - s8[0]))
def B(a2, a3, x): return x + a2 * x**2 + a3 * x**3
def Bint(a2, a3, k):  # x = k * lam, B increasing in x for a2, a3 >= 0
    return (B(a2, a3, k * lam[0]), B(a2, a3, k * lam[1]))
def yint(d, Bi, H):    # y = d * H / (L * B)
    return (d[0] * H / (L[1] * Bi[1]), d[1] * H / (L[0] * Bi[0]))
def ok(yi): return yi[1] ** 100 <= 10 and 10 * yi[0] ** 100 >= 1
def check(name, a2, a3, H):
    B3 = Bint(a2, a3, 2); B7 = Bint(a2, a3, 3)
    y3 = yint(d3, B3, H); y7 = yint(d7, B7, H)
    print(name, 'a2', a2, 'a3', a3, 'H', H, 'y3', [float(v) for v in y3], 'y7', [float(v) for v in y7],
          'ok', ok(y3), ok(y7))
    print('  B3', [float(b) for b in B3], 'B7', [float(b) for b in B7])
    return B3, B7, y3, y7
def line(e, a3):
    x3, x7 = 2 * 0.30103, 3 * 0.30103
    r = (24 - 6 * math.sqrt(2)) / 6 * 10 ** (e / 5)
    return (r * x3 - x7 - a3 * (x7**3 - r * x3**3)) / (x7**2 - r * x3**2)
def Hc(a2, a3):
    x3, x7 = 2 * 0.30103, 3 * 0.30103
    b3 = x3 + a2 * x3**2 + a3 * x3**3; b7 = x7 + a2 * x7**2 + a3 * x7**3
    return math.log(10) * math.sqrt(b3 * b7 / (6 * (24 - 6 * math.sqrt(2))))
if __name__ == '__main__':
    # separation: e = -0.06, a3 near the closest point
    a3 = F(49, 10); a2 = F(round(line(-0.06, 4.9) * 1000), 1000)
    H = F(round(Hc(float(a2), float(a3)) * 10000), 10000)
    check('sep', a2, a3, H)
    A2 = [l * (F(3, 2) - F(3, 4) * F(1, 5)) for l in L]; A3 = [l * l * (F(9, 8) / 25 - F(2, 5) + F(7, 6)) for l in L]
    dd = max((a2 - A2[i])**2 for i in range(2)) + max((a3 - A3[i])**2 for i in range(2))
    print('  sep dist^2 upper', float(dd), '<= 25/16', dd <= F(25, 16))
    # direction: e = -0.087, a3 = 100
    a3 = F(100); a2 = F(round(line(-0.087, 100) * 1000), 1000)
    H = F(round(Hc(float(a2), float(a3)) * 1000), 1000)
    check('dir', a2, a3, H)
    v = min(a2 - L[i] * (F(3, 2) - F(3, 20)) for i in range(2)) - max(7 * lam[j] * (a3 - L[i]**2 * (F(9, 200) - F(2, 5) + F(7, 6))) for i in range(2) for j in range(2))
    print('  dir violation lower bound', float(v))
