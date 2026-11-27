#!/usr/bin/env python3
"""Float plan (not evidence; run 2026-11-27T0828Z): how much the radial step from xi = 2 to 20 amplifies an error in
the start state (L(2), L'(2)) and how L(20) spreads over pieces of the A bracket, for the step 4 (iii) certificate."""
import sys, mpmath as mp
sys.path.insert(0, '../../2026-11-26T1628Z/scripts')
import h2p_float as H
from shoot_A_sens import k1, k2
mp.mp.dps = 60
a = mp.mpf('0.81172958462467962'); b = mp.mpf('0.81172958462484056')
def from2(k, A, L, dL, X=20):
    x = mp.mpf(2)
    while x < X:
        h = min(mp.mpf('0.5') * (x - 1), X - x); L, dL = H.xi_step(k, A, x, L, dL, h); x += h
    return L
for kn, k, A in [('k1', k1, a), ('k2', k2, b)]:
    L0, d0 = H.xi_frob(k, A, 1)
    base = from2(k, A, L0, d0)
    e = mp.mpf('1e-20')
    print(f"{kn}: L(2)={mp.nstr(L0, 12)} L'(2)={mp.nstr(d0, 12)} L(20)={mp.nstr(base, 6)}; "
          f"dL(20)/dL(2)={mp.nstr((from2(k, A, L0 + e, d0) - base) / e, 4)}, dL(20)/dL'(2)={mp.nstr((from2(k, A, L0, d0 + e) - base) / e, 4)}")
