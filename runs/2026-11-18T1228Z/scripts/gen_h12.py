# Exact-rational generator (kept): grid, step constants and H for rl19_box_unmatched_h12
# (flat model Omega = m, far source placed at the middle source).  Every inequality Lean's norm_num
# will check is checked here first with Fractions.
from fractions import Fraction as F
import math, sys
m = F(11, 20)
a2, a3 = F(346, 100), F(163, 100)
lam_lo, lam_hi = F(30101, 100000), F(30105, 100000)
L_lo, L_hi = F(230249, 100000), F(230268, 100000)
s2_lo, s2_hi = F(141421, 100000), F(141422, 100000)
w1 = (F(8408, 10000), F(8409, 10000))   # sqrt(1/sqrt2)   (NCAR.v1_bd)
w3 = (F(5946, 10000), F(5947, 10000))   # sqrt(1/(2sqrt2)) (NCAQ.v3_bd)
def y(v): return m + (1 - m) * v**6
def rdown(x, d=10000): return F(math.floor(x * d), d)
def rup(x, d=10000): return F(math.ceil(x * d), d)
def pieces(lo_start, hi_start, n):
    # lower sum on [hi_start, 1] (integrand decreasing: value at right end), upper on [lo_start, 1]
    lo_pts = [hi_start + (1 - hi_start) * F(i, n) for i in range(n + 1)]
    up_pts = [lo_start + (1 - lo_start) * F(i, n) for i in range(n + 1)]
    lo_pts = [rup(p) if 0 < i < n else p for i, p in enumerate(lo_pts)]
    up_pts = [rup(p) if 0 < i < n else p for i, p in enumerate(up_pts)]
    lo_c, up_c = [], []
    for p, q in zip(lo_pts, lo_pts[1:]):
        c = rdown(2 / math.sqrt(float(y(q))))
        assert y(q) <= (2 / c) ** 2
        lo_c.append(c)
    for p, q in zip(up_pts, up_pts[1:]):
        c = rup(2 / math.sqrt(float(y(p))))
        assert (2 / c) ** 2 <= y(p)
        up_c.append(c)
    Jlo = sum((q - p) * c for p, q, c in zip(lo_pts, lo_pts[1:], lo_c))
    Jup = sum((q - p) * c for p, q, c in zip(up_pts, up_pts[1:], up_c))
    return lo_pts, lo_c, up_pts, up_c, Jlo, Jup
def B(x): return x + a2 * x**2 + a3 * x**3
n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
P1 = pieces(w1[0], w1[1], n); P3 = pieces(w3[0], w3[1], n)
d1 = (s2_lo * P1[4], s2_hi * P1[5]); d3 = (2 * s2_lo * P3[4], 2 * s2_hi * P3[5])
B1 = (B(lam_lo / 2), B(lam_hi / 2)); B3 = (B(3 * lam_lo / 2), B(3 * lam_hi / 2))
# H window from resid_band: 0.98 Lu Bu / dl <= H <= 1.02 Ll Bl / du
win = []
for d, Bb in [(d1, B1), (d3, B3)]:
    win.append((F(98, 100) * L_hi * Bb[1] / d[0], F(102, 100) * L_lo * Bb[0] / d[1]))
Hlo = max(w[0] for w in win); Hhi = min(w[1] for w in win)
print('n', n, 'J1', float(P1[4]), float(P1[5]), 'J3', float(P3[4]), float(P3[5]))
print('H window', float(Hlo), float(Hhi), 'ok' if Hlo < Hhi else 'EMPTY')
if Hlo < Hhi:
    H = rup(Hlo); assert Hlo <= H <= Hhi
    print('H', H)
    for name, P in [('J1', P1), ('J3', P3)]:
        print(name, 'lower pts', [str(p) for p in P[0]], 'c', [str(c) for c in P[1]])
        print(name, 'upper pts', [str(p) for p in P[2]], 'c', [str(c) for c in P[3]])
    print('B1', [float(b) for b in B1], 'B3', [float(b) for b in B3])
    print('d1', [float(v) for v in d1], 'd3', [float(v) for v in d3])
