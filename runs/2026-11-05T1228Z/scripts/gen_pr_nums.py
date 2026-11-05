from fractions import Fraction as F
from mpmath import mp, mpf, sqrt, findroot, polyroots
mp.dps = 50
def m(fr): return mpf(fr.numerator)/fr.denominator
f = lambda x: x**3 - 3*x**2 - 3*x - 3
xc = findroot(f, 4)
X0 = F(39513730, 10**7); X1 = F(39513731, 10**7)
assert f(X0) < 0 < f(X1)
S0 = F(836660026, 10**9); S1 = F(836660027, 10**9)
assert S0*S0 < F(7,10) < S1*S1
K = F(164698, 100000)
D = lambda x: x*x + 2*x - 1
N = lambda x: x*x - 2*x - 1
thc = lambda x: (x-1)**2*(2*x+2)/D(x)**2
print('thc', float(thc(X0)), float(thc(X1)))
al = lambda s: (1 + K*(1-s))**2
# theta = 0.7 thc / alpha; alpha decreasing in s; thc: check monotone
TH0 = F(7,10)*min(thc(X0),thc(X1))/al(S0); TH1 = F(7,10)*max(thc(X0),thc(X1))/al(S1)
print('theta', float(TH0), float(TH1), float(TH1-TH0))
