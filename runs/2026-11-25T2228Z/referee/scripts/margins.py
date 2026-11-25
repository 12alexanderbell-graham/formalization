"""Worst-case margins of the route in task 3(c), with outward-rounded interval arithmetic,
pi in [3.141592, 3.141593], sqrt7 in [2.64575, 2.6458], eps <= 57/10000, |x| <= 1/990."""
from mpmath import iv, mpf
iv.dps = 30
pi = iv.mpf(['3.141592', '3.141593'])
r7 = iv.mpf(['2.64575', '2.6458'])
assert r7.a**2 <= 7 <= r7.b**2
eps_true = iv.sqrt(iv.mpf('3234e-8'))
print("sqrt(3234e-8) =", eps_true, "<= 57/10000:", eps_true.b <= mpf(57) / 10000)
print("1/990 vs sqrt(3234e-8/32):", iv.sqrt(iv.mpf('3234e-8') / 32), iv.mpf(1) / 990)
for E in ['0.0057', '0']:
    eps = iv.mpf(E)
    Lmin = (iv.mpf(pi.a) / (iv.mpf(r7.b) / 2 + 16 * eps)).a
    Lmax = (iv.mpf(pi.b) / (iv.mpf(r7.a) / 2 - 16 * eps)).b
    Rlo = iv.exp(iv.mpf(Lmin)).a
    Rhi = iv.exp(iv.mpf(Lmax)).b
    print(f"eps={E}: L in [{Lmin}, {Lmax}]  e^L in [{Rlo}, {Rhi}]  margins {(iv.mpf(Rlo) - iv.mpf('9.2')).a}, {(iv.mpf('12.9') - Rhi).a}")
    xi = iv.mpf(1) / 990
    fmax = ((2 + xi) / (2 - xi)).b
    fmin = ((2 - xi) / (2 + xi)).a
    most = (-iv.exp(-(1 - 36 * eps) * iv.mpf(Lmin) / 2) * fmax).a
    least = (-iv.exp(-(1 + 36 * eps) * iv.mpf(Lmax) / 2) * fmin).b
    print(f"   deviation quotient in [{most}, {least}]  margins {(iv.mpf(most) + iv.mpf('0.42')).a}, {(iv.mpf('-0.21') - least).a}")
# break-even eps for each of the four inequalities (bisection)
import mpmath as mp
mp.mp.dps = 30
P, Q = mp.mpf('3.141592'), mp.mpf('3.141593'); A, B = mp.mpf('2.64575'), mp.mpf('2.6458')
x = mp.mpf(1) / 990
def ends(e):
    Lmin = P / (B / 2 + 16 * e); Lmax = Q / (A / 2 - 16 * e)
    return (mp.e**Lmin - 9.2, 12.9 - mp.e**Lmax,
            -mp.e**(-(1 - 36 * e) * Lmin / 2) * (2 + x) / (2 - x) + mp.mpf('0.42'),
            mp.mpf('-0.21') + mp.e**(-(1 + 36 * e) * Lmax / 2) * (2 - x) / (2 + x))
for i, nm in enumerate(['R>=9.2', 'R<=12.9', 'D>=-0.42', 'D<=-0.21']):
    lo, hi = mp.mpf(0), mp.mpf('0.04')
    for _ in range(80):
        mid = (lo + hi) / 2
        if ends(mid)[i] > 0: lo = mid
        else: hi = mid
    print(f"largest eps keeping {nm}: {mp.nstr(lo, 6)}")
