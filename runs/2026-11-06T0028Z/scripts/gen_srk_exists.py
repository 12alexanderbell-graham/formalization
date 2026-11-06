"""Brackets for the SRK existence proof (run 2026-11-06T0028Z), exact rationals."""
import json
from fractions import Fraction as F
import sys
C = json.load(open(f"{sys.argv[1] if len(sys.argv) > 1 else 'srk'}_consts.json"))
fr = lambda s: F(*[int(t) for t in s.replace(' ', '').split('/')]) if '/' in s else F(int(s))
T0, T1, PLO, PHI = fr(C['T0']), fr(C['T1']), fr(C['PLO']), fr(C['PHI'])
g = lambda t, x: t/(x-1) - 1/(x*x+x)
c, d = F(6, 5), F(800)
assert g(T0, c) > PHI and g(T1, d) < PLO
assert F(11, 10) <= c <= fr(C['B1']) <= F(7, 5) and F(11, 10) <= fr(C['B1h']) <= F(7, 5) and F(11,10) <= fr(C['A1'])
assert F(400) <= fr(C['A3h']) <= fr(C['B3h']) <= d <= F(1200) and F(400) <= fr(C['A3']) <= F(1200)
assert fr(C['W2b']) <= 400 and fr(C['W1a']) == F(7, 5)
print('ok', float(g(T0, c) - PHI), float(g(T1, d) - PLO))
