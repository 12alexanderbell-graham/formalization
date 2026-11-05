"""Exact-rational chi2_min of the straight-line fit H/(1+z) = a + b z to Moresco+2016 Table 4 + H0 = 73 +- 2.4 at z=0
(Table 5 'linear fit' row), and the arithmetic (k, N) consistency check of all three Table 5 rows."""
from fractions import Fraction as Fr
import math, importlib.util, sys
spec = importlib.util.spec_from_file_location('m16', __file__.replace('_exact', ''))
m16 = importlib.util.module_from_spec(spec); spec.loader.exec_module(m16)
rows = [(Fr(0), Fr(73), Fr('2.4'))] + [(Fr(str(z)), Fr(str(H)) / (1 + Fr(str(z))), Fr(str(s)) / (1 + Fr(str(z)))) for z, H, s in m16.T4]
S = Sx = Sxx = Sy = Sxy = Syy = Fr(0)
for x, y, s in rows:
    w = 1 / s**2; S += w; Sx += w * x; Sxx += w * x * x; Sy += w * y; Sxy += w * x * y; Syy += w * y * y
D = S * Sxx - Sx**2
a = (Sxx * Sy - Sx * Sxy) / D; b = (S * Sxy - Sx * Sy) / D
chi = Syy - a * Sy - b * Sxy
print('line: a =', float(a), ' b =', float(b), ' chi2min =', float(chi), ' (exact rational, denominator digits', len(str(chi.denominator)), ')')
for N in (30, 31):
    print(f'  N={N}: AICc = {float(chi) + 4 + 12/(N-3):.4f} (printed 32.42), BIC = {float(chi) + 2*math.log(N):.4f} (printed 35.29)')
print('AICc - BIC is data-independent: 2k + 2k(k+1)/(N-k-1) - k ln N')
for name, k, aic, bic in (('oLCDM', 3, 21.41, 25.71), ('piecewise', 4, 23.99, 28.72), ('line', 2, 32.42, 35.29)):
    for N in (30, 31):
        d = 2*k + 2*k*(k+1)/(N-k-1) - k*math.log(N)
        print(f'  {name:9s} k={k} N={N}: required {d:+.4f}, printed {aic-bic:+.2f} (rounding tolerance +-0.01)')
