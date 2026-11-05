"""Extra brackets for the PR existence proof (run 2026-11-05T1228Z)."""
import json
from fractions import Fraction as F
C = json.load(open('pr_consts.json'))
fr = lambda s: F(*map(int, s.split(' / '))) if '/' in s else F(int(s))
T0, T1, PLO, PHI = fr(C['T0']), fr(C['T1']), fr(C['PLO']), fr(C['PHI'])
g = lambda t, x: t/(x-1) - 1/(x*x+2*x-1)
c = F(121, 100); d = F(800)
print('g(T0,c)-PHI', float(g(T0,c)-PHI), 'g(T1,d)-PLO', float(g(T1,d)-PLO))
assert g(T0,c) > PHI and g(T1,d) < PLO
assert c < fr(C['A1']) and F(11,10) < c and fr(C['B1']) < F(7,5)
assert F(400) < fr(C['A3h']) and fr(C['B3h']) < d < F(1500) and fr(C['A3']) < d
