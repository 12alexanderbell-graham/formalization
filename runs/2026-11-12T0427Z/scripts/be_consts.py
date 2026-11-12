"""Rational constants for the Bonnor–Ebert assembly (Work/Math/BEMain.lean), checked here exactly."""
import gen_be as BE, g_base as G
from fractions import Fraction as F
import math
sb, cells = BE.run()
g = [c for c in cells if c['kind'] == 'none'][0]
h, B = g['h'], g['B']
lo = lambda p: p[0] - h * sum(abs(c) * h ** k for k, c in enumerate(p[1:]))
hi = lambda p: p[0] + h * sum(abs(c) * h ** k for k, c in enumerate(p[1:]))
D = 10 ** 14
dn = lambda x: F(math.floor(x * D), D)
up = lambda x: F(math.ceil(x * D), D)
C = dict(ELO=dn(lo(g['pe']) - B), EHI=up(hi(g['pe']) + B), PLO=dn(lo(g['pp']) - B), PHI=up(hi(g['pp']) + B),
         EALO=dn(g['pe'][0] - B), EAHI=up(g['pe'][0] + B), PALO=dn(g['pp'][0] - B), PAHI=up(g['pp'][0] + B))
A, Bb = BE.A, BE.B
pi_lo, pi_hi = F(314159265358979323846, 10 ** 20), F(314159265358979323847, 10 ** 20)
C['SQELO'] = dn(math.sqrt(C['EALO'])); assert C['SQELO'] ** 2 <= C['EALO']
while C['SQELO'] ** 2 > C['EALO']: C['SQELO'] -= F(1, D)
C['SQEHI'] = up(math.sqrt(C['EAHI']))
while C['SQEHI'] ** 2 < C['EAHI']: C['SQEHI'] += F(1, D)
C['SPLO'] = dn(math.sqrt(4 * pi_lo))
while C['SPLO'] ** 2 > 4 * pi_lo: C['SPLO'] -= F(1, D)
C['SPHI'] = up(math.sqrt(4 * pi_hi))
while C['SPHI'] ** 2 < 4 * pi_hi: C['SPHI'] += F(1, D)
# checks
assert C['ELO'] > 0 and C['PHI'] < 0
assert 2 * C['ELO'] * C['PHI'] + 2 * C['PLO'] ** 2 / A < 0          # g' < 0 on the bracket cell
GAHI = C['EAHI'] - C['PAHI'] ** 2 / 2                               # g(A) upper bound (φ(A) ≤ PAHI < 0)
mlo = A ** 2 * (-C['PAHI']) * C['SQELO'] / C['SPHI']
mhi = A ** 2 * (-C['PALO']) * C['SQEHI'] / C['SPLO'] + (Bb - A) * Bb ** 2 * GAHI
print('GAHI', float(GAHI))
print('m in', float(mlo), float(mhi), 'margins', float(mlo - F(11822265, 10 ** 7)), float(F(11822266, 10 ** 7) - mhi))
assert mlo >= F(11822265, 10 ** 7) and mhi <= F(11822266, 10 ** 7)
assert 1 / C['EAHI'] >= F(14042032, 10 ** 6) and 1 / C['ELO'] <= F(14042033, 10 ** 6)
assert A >= F(64507514, 10 ** 7) and Bb <= F(64507515, 10 ** 7)
for k, v in C.items():
    print(k, f"({v.numerator}/{v.denominator} : ℚ)" if v.denominator != 1 else v, float(v))
