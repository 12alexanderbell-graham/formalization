"""Rational certificate for vdW uniqueness at T_r = 0.7 (reduced x = v/b, pi = p/P_c).
g(x) = (28/5)/(x-1) - 27/x^2, psi_pi(x) = (28/5) log(x-1) + 27/x - pi x."""
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 40
g = lambda x: Fr(28,5)/(x-1) - Fr(27)/(x*x)
def root(pi, lo, hi, dec):   # bisection on decimal grid
    lo, hi = Fr(lo), Fr(hi)
    s = (g(lo)-pi) > 0
    for _ in range(200):
        m = (lo+hi)/2
        if ((g(m)-pi) > 0) == s: lo = m
        else: hi = m
    return lo
def dec_bracket(r, k):
    a = Fr(int(r*10**k), 10**k); return a, a + Fr(1, 10**k)
plo, phi = Fr(40091,200000), Fr(40093,200000)
out = {}
for name, pi in [('lo', plo), ('hi', phi)]:
    r1 = root(pi, Fr(1001,1000), Fr(17,10), 0); r3 = root(pi, Fr(8), Fr(60), 0)
    a1, b1 = dec_bracket(r1, 6); a3, b3 = dec_bracket(r3, 5)
    assert g(a1) > pi > g(b1) and g(a3) > pi > g(b3)
    F = lambda q: mp.mpf(q.numerator)/q.denominator
    def ps(x, p): return mp.mpf(28)/5*mp.log(F(x-1)) + F(27/x - p*x)
    if name == 'lo':
        K = ps(a3, pi) - ps(b1, pi) - F((b1-a1)*(pi-g(b1)))
        Q = (a3-1)/(b1-1)
    else:
        K = ps(b3, pi) - ps(b1, pi) + F((b3-a3)*(pi-g(b3)))
        Q = (b3-1)/(b1-1)
    print(name, 'pi', pi, 'a1', a1, 'b1', b1, 'a3', a3, 'b3', b3)
    print('   K', K, ' Q', Q, float(Q), ' x=1-Q/64', float(1-Q/64))
