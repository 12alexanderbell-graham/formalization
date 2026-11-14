"""Emit Work/Math/BEHData.lean from gen_bh.py's cells (run 2026-11-14T0428Z)."""
import json, sys
from fractions import Fraction as F
cells = json.load(open(sys.argv[1]))
out = sys.argv[2]
FU, FV, R = sys.argv[3], sys.argv[4], sys.argv[5]
SEG = 15
def q(x):
    x = F(x)
    return '(%d : ℚ)' % x.numerator if x.denominator == 1 else '(%d/%d : ℚ)' % (x.numerator, x.denominator)
L = ['import Work.Math.BEHCell', '',
     '/-! Bonnor–Ebert sphere, `BEHData`: the validated cells of the regular isothermal solution in homology',
     'variables on [7, 150] as data (generator `runs/2026-11-14T0428Z/scripts/gen_bh.py`, emitter `emit_bh.py`),',
     'each segment decided by kernel evaluation: 2u − v < 0 up to the bracket cell of the first minimum of',
     'the mass, 6u − 2u² − 3uv + v > 0 on the bracket cell, 2u − v > 0 after it. -/', '',
     'namespace Work.Math.BEHData', 'open Work.Math.BEHCell', '']
for i, c in enumerate(cells):
    f = [c[k] for k in ('t0', 'h', 'delta', 'eps', 'B', 'UL', 'UH', 'VL', 'VH', 'L1', 'L2', 'K')]
    L.append('def c%d : Cell := ⟨%s,' % (i, ', '.join(q(x) for x in f)))
    L.append('  [%s],' % ', '.join(q(x) for x in c['pu']))
    L.append('  [%s]⟩' % ', '.join(q(x) for x in c['pv']))
L.append('')
kinds = [c['kind'] for c in cells]
ib = kinds.index('br')
n = len(cells)
segs = []
# dec segments: 0..ib-1, terminating in link to next segment start or bracket
starts = list(range(0, ib, SEG))
for j, s0 in enumerate(starts):
    e = min(s0 + SEG, ib)
    segs.append(('dec%d_ok' % j, 2, list(range(s0, e)), 'fun e => linkOK e c%d' % e))
L.append('theorem br_ok : cellOK (7 : ℚ) 150 3 c%d = true := by\n  decide +kernel\n' % ib)
L.append('theorem br_link : linkOK c%d c%d = true := by\n  decide +kernel\n' % (ib, ib + 1))
starts = list(range(ib + 1, n, SEG))
for j, s0 in enumerate(starts):
    e = min(s0 + SEG, n)
    term = ('fun e => linkOK e c%d' % e) if e < n else 'endOK 150 %s %s %s' % (FU, FV, R)
    segs.append(('inc%d_ok' % j, 1, list(range(s0, e)), term))
for name, m, idx, term in segs:
    L.append('theorem %s : chainTo (7 : ℚ) 150 %d (%s) [%s] = true := by\n  decide +kernel\n' %
             (name, m, term, ', '.join('c%d' % i for i in idx)))
L.append('end Work.Math.BEHData')
open(out, 'w').write('\n'.join(L) + '\n')
print('bracket index', ib, 'cells', n, 'segments', len(segs), file=sys.stderr)
