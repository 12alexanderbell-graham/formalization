# Run 2026-11-12T2228Z: copy of runs/2026-11-12T1828Z/scripts/plan_rev.py for the remaining rows of Ganapol 2010 Table 7
# (beta = -0.01 ... -0.09, -0.11 ... -0.14, -0.16). q0 = float shooting (runs/2026-11-12T1828Z/scripts/shoot_rev.py,
# DOP853 rtol 1e-13), log in ../shoot.log. Window lo < q0 < hi = lo + 1e-10; shooting values halfway to each end (cap).
import json, math, sys
from fractions import Fraction as Fr
rows = {'01': ('100', -0.042320926039157596), '02': ('50', -0.06516858554290365), '03': ('100/3', -0.08256296511875821),
        '04': ('25', -0.0966367874085913), '05': ('20', -0.10827108328583358), '06': ('50/3', -0.11792411103838696),
        '07': ('100/7', -0.12585853172238534), '08': ('25/2', -0.13222765437970213), '09': ('100/9', -0.13711381180237442),
        '11': ('100/11', -0.14250791030933943), '12': ('25/3', -0.14293519435759988), '13': ('100/13', -0.14170950215217404),
        '14': ('50/7', -0.13863892525436244), '16': ('25/4', -0.12556766421725582)}
cap = float(sys.argv[1]) if len(sys.argv) > 1 else 2e-11
# slow-side shooting value at q0 + FRAC_HI*(hi - q0) (default 1/2; row 09 has 2.4e-12 to its upper end and its
# halfway slow chain failed the end condition by 6.5e-13)
FRAC_HI = {'09': 0.85}
out = {}
for tag, (Ks, q0) in rows.items():
    K = Fr(Ks); sK = math.sqrt(float(K))
    assert K == Fr(100, int(tag))
    lo = math.floor(q0 * 1e10); hi = lo + 1
    qlo = lo * 1e-10; qhi = hi * 1e-10
    qo = max((qlo + q0) / 2, q0 - cap); qs = min(q0 + FRAC_HI.get(tag, 0.5) * (qhi - q0), q0 + cap)
    Ao = Fr(round(qo * sK * 1e15), 10**15); As = Fr(round(qs * sK * 1e15), 10**15)
    Ac = (Ao + As) / 2; R0 = (As - Ao) / 2 + Fr(1, 10**15)
    out[tag] = dict(K=Ks, q0=q0, lo=lo, margin_lo=q0 - qlo, margin_hi=qhi - q0,
                    Aover=str(Ao), Aslow=str(As), Ac=str(Ac), R0=str(R0))
    print(tag, Ks, lo, '%.2e %.2e' % (q0 - qlo, qhi - q0))
json.dump(out, open('runs/2026-11-12T2228Z/scripts/rows_rev.json', 'w'), indent=1)
