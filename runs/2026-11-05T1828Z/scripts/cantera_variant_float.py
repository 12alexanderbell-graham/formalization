"""Floating point (run 2026-11-05T1828Z, not certified): omega_out of Peng-Robinson with Soave alpha for three
versions of the 1978 kappa(omega): the consensus coefficients (thermo, pychemqt, DWSIM, four arXiv papers),
Cantera's code (src/thermo/PengRobinson.cpp, main, fetched 2026-11-05) and Cantera's header documentation.
Reuses run 1228Z's pr_float.py (Maxwell equal areas via the closed-form primitive)."""
from mpmath import mp, mpf
src = open('../../2026-11-05T1228Z/scripts/pr_float.py').read().split("print('xc'")[0]
src = src.replace("def run(omega):\n    k = mpf('0.37464') + mpf('1.54226')*omega - mpf('0.26992')*omega**2", "def run(k):")
mp.dps = 30
exec(src)
V = {'consensus': ('0.379642', '1.48503', '0.164423', '0.016666'),
     'cantera_code': ('0.374642', '1.487503', '0.164423', '0.016666'),
     'cantera_doc': ('0.379642', '1.487503', '0.164423', '0.016667')}
for w in ['0.6', '0.8', '1', '1.2', '1.5']:
    W = mpf(w); row = [w]
    for name, (a, b, c, d) in V.items():
        k = mpf(a) + mpf(b)*W - mpf(c)*W**2 + mpf(d)*W**3
        row.append(f"{name} {mp.nstr(run(k)['omega'], 7)}")
    print('  '.join(row), flush=True)
