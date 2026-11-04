# Certificates for the non-vacuity witness of fit_direction at Ω = 1/5 (Work/Cosmography/B1FitWitness.lean).
from gen_fit import *
import mpmath as mp
Om = F(1, 5); N = 12
out = []
vals = {}
for k in (1, 3, 5):
    lc = lower_cert(k, Om, N); uc = upper_cert(k, Om, Om, N)
    s_l = emit_lower(f"WL{k}", lc); s_u = emit_upper(f"WU{k}", uc)
    vals[k] = (lc['A_'] - lc['B_'] * Om, uc['C_'] + uc['D_'] * Om)
    out += [s_l, s_u]
open('/tmp/claude-0/witness_certs.lean', 'w').write("\n".join(out))
for k in (1, 3, 5):
    lo, hi = vals[k]
    print(k, float(lo), float(hi), str(lo), str(hi))
