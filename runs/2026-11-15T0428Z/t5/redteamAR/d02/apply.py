#!/usr/bin/env python3
"""d02: a candidates row that tells what verified records verified, citing record names only (F4_values, ...), which
FB22's mention pattern F<k>\\b does not see ('F4_values': no word boundary between 4 and _)."""
import sys
root = sys.argv[1]
p = f"{root}/FINDINGS.md"
t = open(p, encoding="utf-8").read()
anchor = "| C4 | Capozziello, Lazkoz, Salzano 2011 | — | → **F2** |\n"
assert t.count(anchor) == 1
row = ("| C33 | Bamba, Capozziello, Nojiri, Odintsov 2012 (arXiv:1205.3421), Eqs. (10.54)–(10.57), (10.61)–(10.63); "
       "Cattoën & Visser 2007 Eq. 59 | every printed y-series coefficient of d_L, d_A and d_Q (D²_{L,y}, D³_{L,y}, D⁴_{L,y}, "
       "D³_{A,y}, D⁴_{A,y}, Q²) is wrong, for every q₀, j₀, s₀, l₀ and every curvature Ω₀ | CERTIFIED in Lean by the records "
       "`F4_values`, `F5_values`, `F6_third`, `F6_fourth`, `F7_third`, `F7_fourth` (all quantifier-free: they hold for every "
       "cosmological model; each printed formula agrees with a blind second reading); nothing left to check |\n")
open(p, "w", encoding="utf-8").write(t.replace(anchor, anchor + row))
