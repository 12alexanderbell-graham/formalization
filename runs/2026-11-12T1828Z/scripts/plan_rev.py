# Run 2026-11-12T1828Z: ten-decimal windows and rational shooting values for the reversed-flow rows.
# For each row: q0 (float shooting), window lo < q0 < hi = lo + 1e-10, A_over = sqrt(K)*(lo+q0)/2 rounded,
# A_slow = sqrt(K)*(q0+hi)/2 rounded (each at most 'cap' from q0 in q), tube centre/radius covering both.
import json, math, sys
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
getcontext().prec = 40
rows = {'17': ('100/17', -0.11422723909825624), '18': ('50/9', -0.09769206013457485),
        '19': ('100/19', -0.07133590600344236), '15': ('20/3', -0.13342123789528923)}
cap = float(sys.argv[1]) if len(sys.argv) > 1 else 2e-11
out = {}
for tag, (Ks, q0) in rows.items():
    K = Fr(Ks); sK = math.sqrt(float(K))
    lo = math.floor(q0 * 1e10); hi = lo + 1           # in units of 1e-10
    qlo = lo * 1e-10; qhi = hi * 1e-10
    qo = max((qlo + q0) / 2, q0 - cap); qs = min((q0 + qhi) / 2, q0 + cap)
    Ao = Fr(round(qo * sK * 1e15), 10**15); As = Fr(round(qs * sK * 1e15), 10**15)
    Ac = (Ao + As) / 2; R0 = (As - Ao) / 2 + Fr(1, 10**15)
    out[tag] = dict(K=Ks, q0=q0, lo=lo, margin_lo=q0 - qlo, margin_hi=qhi - q0,
                    Aover=str(Ao), Aslow=str(As), Ac=str(Ac), R0=str(R0))
    print(tag, out[tag])
json.dump(out, open('runs/2026-11-12T1828Z/scripts/rows_rev.json', 'w'), indent=1)
