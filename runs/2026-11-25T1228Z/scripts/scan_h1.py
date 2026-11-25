"""Float scan for hypothesis 1 (density >= 1/10) of the curved pair, closed or flat side (run 2026-11-25T1228Z, for the
next part-1 run). For m below 1/10 and k in [-1/10, 0]: the minimum of the radicand y(v) = m(1 - v^6) + k(v^2 - v^6) + v^6
on [w5, 1] (negative: no model reaches the farther source), and where it is positive the ratio of the integral from a
cut point vc above w5 to J3, against the 27/10 / 2 = 1.35 the closed proof needs (sine correction ignored here)."""
from mpmath import mp, quad, sqrt, mpf
mp.dps = 15
w3 = sqrt(1/(2*sqrt(2))); w5 = sqrt(1/(4*sqrt(2)))
def y(m, k, v): return m*(1 - v**6) + k*(v**2 - v**6) + v**6
def miny(m, k):
    return min(y(m, k, w5 + (1 - w5)*i/400) for i in range(401))
def J(m, k, a): return quad(lambda v: 2/sqrt(y(m, k, v)), [a, 1])
print('k, m at which min y on [w5,1] crosses zero (bisection):')
for k in [0, -0.025, -0.05, -0.075, -0.1]:
    lo, hi = mpf(-0.05), mpf(0.1)
    for _ in range(40):
        mid = (lo + hi)/2
        if miny(mid, k) > 0: hi = mid
        else: lo = mid
    print(' k=%6.3f  m_edge=%.5f' % (k, float(hi)))
print('ratio int_{vc}^1 / J3 at reachable points (needs >= 1.35):')
for k in [0, -0.05, -0.1]:
    for m in [0.1, 0.05, 0.02, 0.012, 0.0]:
        if miny(m, k) <= 0: print(' k=%5.2f m=%5.3f unreachable' % (k, m)); continue
        J3 = J(m, k, w3)
        row = ['k=%5.2f m=%5.3f J5/J3=%.3f' % (k, m, J(m, k, w5)/J3)]
        for vc in [0.45, 0.5]:
            row.append('vc=%.2f: %.3f' % (vc, J(m, k, vc)/J3))
        print(' ', '  '.join(row))
