"""Referee: exact-rational check of short decimal witnesses for oL_bic_exceeds and line_bic_exceeds
(the oLCDM chi2 needs sqrt, so it is evaluated with mpmath at 50 digits). Run: python3 -I referee_m16_witness.py"""
from fractions import Fraction as Fr
import importlib.util, mpmath as mp
spec = importlib.util.spec_from_file_location('r', __file__.replace('_witness', ''))
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)
mp.mp.dps = 50
rows = R.table()
def chi_line(a, b):
    s = sum((a + b*Fr(z) - Fr(H)/(1+Fr(z)))**2 / (Fr(sg)/(1+Fr(z)))**2 for z, H, sg in rows)
    return s + (a - 73)**2 / Fr('2.4')**2
for a, b in ((Fr('67.13'), Fr('-4.586')), (Fr('67.133'), Fr('-4.586')), (Fr('67.1328'), Fr('-4.5859'))):
    c = chi_line(a, b)
    print(f'line witness a={a}, b={b}: chi2 = {float(c):.9f}  (<27.972: {c < Fr("27.972")}); chi2+2ln35 = {float(c)+2*float(mp.log(35)):.6f} (<35.285)')
for w in (('72.29', '0.436', '0.981'), ('72.2865', '0.4362', '0.9814')):
    H0, Om, OL = map(mp.mpf, w)
    c = R.chi2_full(H0, Om, OL, rows)
    ok = Om <= 2*OL <= mp.mpf('15.625')*Om and 0 <= Om <= 1
    print(f'oLCDM witness {w}: chi2 = {mp.nstr(c, 12)} (<14.975: {c < mp.mpf("14.975")}), in wedge {ok}, '
          f'chi2+3ln35 = {mp.nstr(c+3*mp.log(35), 10)} (<25.705)')
