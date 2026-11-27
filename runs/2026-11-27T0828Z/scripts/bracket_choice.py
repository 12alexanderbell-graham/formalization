#!/usr/bin/env python3
"""Float plan (not evidence; run 2026-11-27T0828Z): the A bracket [a, b] for which the radial events can hold.
The radial shooting value L(20) moves by about -2.6e8 per unit of A, so `hunder` (k1, every A in [a, b]) and
`hover` (k2, every A in [a, b]) need b - A(k1) and A(k2) - a below about 1.5e-13 (run 1628Z's widening by 1e-12
makes both false: shoot_A_sens.py). Prints A(k1), A(k2) and L(20) at the corners of the candidate bracket."""
import sys, mpmath as mp
sys.path.insert(0, '../../2026-11-26T1628Z/scripts')
import h2p_float as H
from shoot_A_sens import shootA, k1, k2
mp.mp.dps = 60
A1 = H.A_of_k(k1); A2 = H.A_of_k(k2)
print("A(k1) =", mp.nstr(A1, 22)); print("A(k2) =", mp.nstr(A2, 22))
d = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf('4e-14')
a = mp.floor((A1 - d) * 10**17) / 10**17; b = mp.ceil((A2 + d) * 10**17) / 10**17
print("a =", mp.nstr(a, 20), " b =", mp.nstr(b, 20))
for X in [15, 20]:
    print(f"X={X}: under k1,A=b L={mp.nstr(shootA(k1, b, X)[0], 6)}; under k1,A=a L={mp.nstr(shootA(k1, a, X)[0], 6)}; "
          f"over k2,A=a L={mp.nstr(shootA(k2, a, X)[0], 6)}; over k2,A=b L={mp.nstr(shootA(k2, b, X)[0], 6)}")
