#!/usr/bin/env python3
"""Feasibility of the hlo/hhi certificate (run 2026-11-27T0828Z): interval recurrence of the angular
coefficients b_n(k, A) over k in [k1, k2] at fixed rational A, outward-rounded to multiples of 2^-P,
partial sum of g = sum (n+1) b_{n+1} up to N, tail by the uniform bound |b_n| <= (9/4)^9 (2/3)^n."""
from fractions import Fraction as F
import math, sys
k1 = F(22052684289898, 10**13); k2 = F(22052684289900, 10**13)
P = int(sys.argv[1]) if len(sys.argv) > 1 else 160
N = int(sys.argv[2]) if len(sys.argv) > 2 else 130
D = 2**P
def rd(x): return F(math.floor(x * D), D)
def ru(x): return F(math.ceil(x * D), D)
def imul(a, b):
    ps = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return (min(ps), max(ps))
def iadd(a, b): return (a[0]+b[0], a[1]+b[1])
def iscale(c, a): return (c*a[0], c*a[1]) if c >= 0 else (c*a[1], c*a[0])
def rnd(a): return (rd(a[0]), ru(a[1]))
K = (k1, k2)
def coeffs(A):
    b = [(F(1), F(1))]
    b.append(rnd(((A - k2)/2, (A - k1)/2)))
    t = imul(iadd((F(2)+A-k2, F(2)+A-k1), (F(0), F(0))), b[1])
    b.append(rnd(iscale(F(1, 8), iadd(t, (2*k1, 2*k2)))))
    for n in range(0, N):
        c = (F((n+2)*(n+3)) - k2 + A, F((n+2)*(n+3)) - k1 + A)
        s = iadd(iadd(imul(c, b[n+2]), imul(iscale(2, K), b[n+1])), iscale(-1, imul(K, b[n])))
        b.append(rnd(iscale(F(1, 2*(n+3)**2), s)))
    return b
CB = F(9, 4)**9
def g_enclosure(A):
    b = coeffs(A)
    lo = sum(F(n+1)*b[n+1][0] for n in range(N)); hi = sum(F(n+1)*b[n+1][1] for n in range(N))
    # tail: sum_{n>=N} (n+1) CB (2/3)^(n+1) = CB * sum_{m>=N+1} m q^m, q = 2/3
    q = F(2, 3); m0 = N + 1
    tail = CB * q**m0 * (m0 / (1 - q) + q / (1 - q)**2)
    return lo - tail, hi + tail, tail, max(x[1]-x[0] for x in b[N-5:N])
for A in [F(811729584623719, 10**15), F(811729584625801, 10**15)]:
    lo, hi, tail, w = g_enclosure(A)
    print(f"A={float(A):.15f}: g in [{float(lo):.4e}, {float(hi):.4e}] tail {float(tail):.2e}")
