"""Extra brackets for the existence proof (run 2026-11-04T1828Z)."""
from fractions import Fraction as F
T0 = F(1187001329, 10**10); T1 = F(593500771, 5*10**9)
PLO = F(2569, 2000000); PHI = F(12849, 10**7)
g = lambda t, x: t/(x-1) - 1/(x*x+x)
c = F(139,100); d = F(87,1)
print('g(T0,c)-PHI', float(g(T0,c)-PHI), 'g(T1,d)-PLO', float(g(T1,d)-PLO))
assert g(T0,c) > PHI and g(T1,d) < PLO
