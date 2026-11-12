#!/usr/bin/env python3
"""Run 2026-11-12T1428Z: attached Falkner-Skan rows by the generic K stack (Checked/FSAtt).
For each beta: K = -1/beta, window (lo, hi) = the 10-decimal floor/ceil of the float shooting value q,
shooting values A_lo, A_hi (rationals, 13 decimals) strictly between sqrt(K)*lo, sqrt(K)*q and sqrt(K)*q, sqrt(K)*hi.
Float shooting (scipy DOP853, rtol 1e-12, L = 10 and 12) only chooses the numbers; the exact generator certifies them."""
import json, sys, subprocess, os
from fractions import Fraction as Fr
from mpmath import mp, mpf, sqrt, floor, ceil
mp.dps = 40
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
def res(a, b, L):
    s = solve_ivp(lambda t, y: [y[1], y[2], -y[0]*y[2] - b*(1 - y[1]**2)], [0, L], [0, 0, a], rtol=1e-13, atol=1e-15, method='DOP853')
    return s.y[1, -1] - 1
ROWS = {'15': Fr(-15, 100), '17': Fr(-17, 100), '18': Fr(-18, 100), '19': Fr(-19, 100), '195': Fr(-195, 1000), '198': Fr(-198, 1000)}
out = {}
for tag, b in ROWS.items():
    qs = [brentq(lambda a: res(a, float(b), L), 1e-3, 0.5, xtol=1e-16) for L in (10, 12)]
    q = mpf(qs[1]); K = -1 / b; s = sqrt(mpf(K.numerator) / K.denominator)
    lo = floor(q * 10**10) / 10**10; hi = lo + mpf(1) / 10**10
    Alo = Fr(int(floor((s * lo + s * q) / 2 * 10**13)), 10**13)
    Ahi = Fr(int(ceil((s * hi + s * q) / 2 * 10**13)), 10**13)
    out[tag] = dict(beta=str(b), K=str(K), q=[float(x) for x in qs], lo=int(floor(q*10**10)), Alo=str(Alo), Ahi=str(Ahi))
    print(tag, out[tag])
json.dump(out, open(sys.argv[1], 'w'), indent=1)
