#!/usr/bin/env python3
"""Feasibility of the hM certificate (run 2026-11-27T0828Z): M(k, A, s) = sum b_n s^n > 0 for k in [k1, k2],
A in [a, b], s in [0, 1], by exact rational interval arithmetic on pieces [j/P, (j+1)/P] of [0, 1];
tail |sum_{n>=N} b_n s^n| <= 3 CB (2/3)^N."""
from fractions import Fraction as F
import sys
k1 = F(22052684289898, 10**13); k2 = F(22052684289900, 10**13)
a = F(811729584623719, 10**15); b = F(811729584625801, 10**15)
N = int(sys.argv[1]); P = int(sys.argv[2])
def imul(x, y):
    ps = [x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1]]; return (min(ps), max(ps))
def iadd(x, y): return (x[0]+y[0], x[1]+y[1])
def ineg(x): return (-x[1], -x[0])
def ismul(c, x): return (c*x[0], c*x[1])
K = (k1, k2); AI = (a, b)
def run(SI):
    b0 = (F(1), F(1)); b1 = ((AI[0]-K[1])/2, (AI[1]-K[0])/2)
    b2 = ismul(F(1, 8), iadd(imul((2-K[1]+AI[0], 2-K[0]+AI[1]), b1), ismul(2, K)))
    m = (F(0), F(0)); pw = (F(1), F(1))
    for n in range(N):
        c = ((n+2)*(n+3) - K[1] + AI[0], (n+2)*(n+3) - K[0] + AI[1])
        num = iadd(iadd(imul(c, b2), imul(ismul(2, K), b1)), ineg(imul(K, b0)))
        m = iadd(m, imul(b0, pw)); pw = imul(pw, SI)
        b0, b1, b2 = b1, b2, ismul(F(1, 2*(n+3)**2), num)
    return m
CB = F(9, 4)**9; tail = 3*CB*F(2, 3)**N
worst = min(run((F(j, P), F(j+1, P)))[0] for j in range(P)) - tail
print(N, P, float(tail), float(worst))
