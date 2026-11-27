#!/usr/bin/env python3
"""Float check (not evidence; run 2026-11-27T0828Z): does UnderIVP k1 A / OverIVP k2 A hold for every A of the
certified angular bracket [a, b] = [0.811729584623719, 0.811729584625801]? Radial L at X = 15, 20 for k = k1, k2 and
A = a, b (mpmath, 60 digits, series steps of run 1628Z's h2p_float.py)."""
import sys, mpmath as mp
sys.path.insert(0, '../../2026-11-26T1628Z/scripts')
import h2p_float as H
mp.mp.dps = 60
def shootA(k, A, X):
    x = mp.mpf(2); L, dL = H.xi_frob(k, A, x - 1)
    while x < X:
        h = min(mp.mpf('0.5') * (x - 1), X - x); L, dL = H.xi_step(k, A, x, L, dL, h); x += h
    return L, dL
k1 = mp.mpf(22052684289898) / 10**13; k2 = mp.mpf(22052684289900) / 10**13
a = mp.mpf(811729584623719) / 10**15; b = mp.mpf(811729584625801) / 10**15
if __name__ == "__main__":
  for X in [15, 20]:
      for kn, k in [('k1', k1), ('k2', k2)]:
          for An, A in [('a', a), ('b', b), ('A(k)', H.A_of_k(k))]:
              L, dL = shootA(k, A, X)
              print(f"X={X} {kn} {An}: L={mp.nstr(L, 8)} dL={mp.nstr(dL, 8)}")
