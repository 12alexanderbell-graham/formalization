"""Certificate generator for Work/Data/Moresco16.lean (run 2026-11-05T0428Z).
Exact rationals: at a rational point (H0, Om, OL) bound each chi^2 term from above using
|sqrt(y) - s| <= eps (s, eps rational), and evaluate the line chi^2 exactly."""
from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec = 50
T = [(0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
 (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
 (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9),
 (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
 (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
 (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]
T = [(F(str(z)), F(str(h)), F(str(s))) for z, h, s in T]
H0, Om, OL = F('72.2865'), F('0.43617'), F('0.98144')
EPS = F(1, 10**9)
def E2(z): return Om*(1+z)**3 + (1-Om-OL)*(1+z)**2 + OL
tot = F(0); rows = []
for z, h, s in T:
    y = E2(z)
    r = Decimal(y.numerator)/Decimal(y.denominator)
    sq = F(str(round(r.sqrt(), 12)))
    assert (sq-EPS)**2 <= y <= (sq+EPS)**2 and sq - EPS >= 0
    m = H0*sq - h
    A = F(str(round(abs(Decimal(m.numerator)/Decimal(m.denominator)), 6))) + F(1, 10**6)
    assert -A <= m <= A
    U = (A + H0*EPS)**2 / s**2
    Ur = F(str(round(Decimal(U.numerator)/Decimal(U.denominator) + Decimal('1e-6'), 6)))
    assert U <= Ur
    rows.append((sq, A, Ur)); tot += Ur
prior = (H0-73)**2/F('2.4')**2
print('oLCDM upper bound', float(tot+prior))
# line
a, b = F('67.13281'), F('-4.58592')
chil = sum(((a + b*z) - h/(1+z))**2 / (s/(1+z))**2 for z, h, s in T) + (a-73)**2/F('2.4')**2
print('line chi2 at point', float(chil))
import json, sys
json.dump({'rows': [[str(x) for x in r] for r in rows]}, open(sys.argv[1], 'w') if len(sys.argv) > 1 else sys.stdout)
