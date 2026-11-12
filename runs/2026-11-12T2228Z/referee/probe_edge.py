#!/usr/bin/env python3
"""Referee: re-evaluate the extra F sign changes the coarse (h=0.5) scan reported next to the blow-up edge at L=20."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from fs_taylor import F
mp.mp.dps = 30
for b, lo in (('-0.06', -1650), ('-0.16', -3000)):
    vals = [(s, F(mp.mpf(b), s, 20, mp.mpf('0.25'), 22)) for s in [mp.mpf(lo + 5 * i) / 10000 for i in range(8)]]
    print(b, [(float(s), None if v is None else round(float(v), 4)) for s, v in vals], flush=True)
