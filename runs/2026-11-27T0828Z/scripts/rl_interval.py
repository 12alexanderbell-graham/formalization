#!/usr/bin/env python3
"""Feasibility of RL > 0 on u in [0, 1] (OverIVP's Frobenius part; run 2026-11-27T0828Z): the radial Frobenius
coefficients fc(1, 4 - k + A, 4 - 2k, -k) on intervals (A in [a, b], k = k2), u in P pieces, N terms, tail
3 * 12^19 * (2/3)^N. Usage: rl_interval.py N P"""
from fractions import Fraction as F
import sys
k = F(22052684289900, 10**13)
a = F('0.81172958462467962'); b = F('0.81172958462484056')
N = int(sys.argv[1]); P = int(sys.argv[2])
def imul(x, y):
    ps = [x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1]]; return (min(ps), max(ps))
def iadd(x, y): return (x[0]+y[0], x[1]+y[1])
def ineg(x): return (-x[1], -x[0])
def ismul(c, x): return (c*x[0], c*x[1]) if c >= 0 else (c*x[1], c*x[0])
v0 = (4 - k + a, 4 - k + b); v1 = 4 - 2*k; v2 = -k
def run(U):
    c0 = (F(1), F(1)); c1 = ismul(F(-1, 2), v0)
    c2 = ismul(F(1, 8), iadd(imul(ineg(iadd((F(2), F(2)), v0)), c1), (-v1, -v1)))
    m = (F(0), F(0)); pw = (F(1), F(1))
    for n in range(N):
        t = ineg(iadd(((n+2)*(n+3), (n+2)*(n+3)), v0))
        num = iadd(iadd(imul(t, c2), ismul(-v1, c1)), ismul(-v2, c0))
        m = iadd(m, imul(c0, pw)); pw = imul(pw, U)
        c0, c1, c2 = c1, c2, ismul(F(1, 2*(n+3)**2), num)
    return m
tail = 3 * F(12)**19 * F(2, 3)**N
lows = [run((F(j, P), F(j+1, P)))[0] - tail for j in range(P)]
print(N, P, float(tail), float(min(lows)))
