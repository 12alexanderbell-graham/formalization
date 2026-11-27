#!/usr/bin/env python3
"""Emulation of the tight-bracket hlo/hhi certificate (run 2026-11-27T0828Z): exact rational interval recurrence
(as Work/Quantum/AngularCert.lean `run`, no rounding) over P equal pieces of the k-window, N terms.
Usage: g_pieces.py a b P N"""
from fractions import Fraction as F
import sys
k1 = F(22052684289898, 10**13); k2 = F(22052684289900, 10**13)
a = F(sys.argv[1]); b = F(sys.argv[2]); P = int(sys.argv[3]); N = int(sys.argv[4])
def imul(x, y):
    ps = [x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1]]; return (min(ps), max(ps))
def iadd(x, y): return (x[0]+y[0], x[1]+y[1])
def ineg(x): return (-x[1], -x[0])
def ismul(c, x): return (c*x[0], c*x[1])
def gs(K, A):
    AI = (A, A)
    b0 = (F(1), F(1)); b1 = ((AI[0]-K[1])/2, (AI[1]-K[0])/2)
    b2 = ismul(F(1, 8), iadd(imul((2-K[1]+AI[0], 2-K[0]+AI[1]), b1), ismul(2, K)))
    g = (F(0), F(0))
    for n in range(N):
        c = ((n+2)*(n+3) - K[1] + AI[0], (n+2)*(n+3) - K[0] + AI[1])
        num = iadd(iadd(imul(c, b2), imul(ismul(2, K), b1)), ineg(imul(K, b0)))
        g = iadd(g, ismul(n+1, b1))
        b0, b1, b2 = b1, b2, ismul(F(1, 2*(n+3)**2), num)
    return g
tail = F(9, 4)**9 * F(2, 3)**(N+1) * (3*N+9)
w = (k2 - k1) / P
his = [gs((k1 + i*w, k1 + (i+1)*w), a)[1] + tail for i in range(P)]
los = [gs((k1 + i*w, k1 + (i+1)*w), b)[0] - tail for i in range(P)]
print(f"P={P} N={N}: max upper g(k,a) = {float(max(his)):.3e}; min lower g(k,b) = {float(min(los)):.3e}")
