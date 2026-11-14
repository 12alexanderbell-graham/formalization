"""Emit Work/Math/BEH2Data.lean from gen_bh2.py's cells (run 2026-11-14T1028Z; adapted from run 0428Z's emit_bh.py).
Cells on [150, 2000]: 2u - v > 0 (invariant 1) up to the bracket cell of the second maximum, the bracket cell
(invariant 0 plus a separate check of 6u - 2u^2 - 3uv + v < 0), 2u - v < 0 (invariant 2) after it."""
import json, sys
from fractions import Fraction as F
cells = json.load(open(sys.argv[1]))
out = sys.argv[2]
FU, FV, R = sys.argv[3], sys.argv[4], sys.argv[5]
SEG = 15
def q(x):
    x = F(x)
    return '(%d : ℚ)' % x.numerator if x.denominator == 1 else '(%d/%d : ℚ)' % (x.numerator, x.denominator)
L = ['import Checked.Math.BEHCell', '',
     '/-! Bonnor–Ebert sphere, `BEH2Data`: the validated cells of the regular isothermal solution in homology',
     'variables from the end radius of `BEHChain` to the start of the tail, as data (generator',
     '`runs/2026-11-14T1028Z/scripts/gen_bh2.py`, emitter `emit_bh2.py`), each segment decided by kernel',
     'evaluation: 2u − v > 0 up to the bracket cell of the second maximum of the mass, the bracket cell, and',
     '2u − v < 0 after it. -/', '',
     'namespace Work.Math.BEH2Data', 'open Checked.Math.BEHCell', 'open Checked.Math.GCellQ (lo hi)', '']
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
starts = list(range(0, ib, SEG))
for j, s0 in enumerate(starts):
    e = min(s0 + SEG, ib)
    segs.append(('inc%d_ok' % j, 1, list(range(s0, e)), 'fun e => linkOK e c%d' % e))
L.append('theorem br_ok : cellOK (150 : ℚ) 2000 0 c%d = true := by\n  decide +kernel\n' % ib)
L.append('theorem br_G : decide (hi (Gp c%d) c%d.h + (7 + 7 * c%d.UH + 3 * c%d.VH) * c%d.B < 0) = true := by\n  decide +kernel\n' % ((ib,) * 5))
L.append('theorem br_link : linkOK c%d c%d = true := by\n  decide +kernel\n' % (ib, ib + 1))
starts = list(range(ib + 1, n, SEG))
for j, s0 in enumerate(starts):
    e = min(s0 + SEG, n)
    term = ('fun e => linkOK e c%d' % e) if e < n else 'endOK 2000 %s %s %s' % (FU, FV, R)
    segs.append(('dec%d_ok' % j, 2, list(range(s0, e)), term))
for name, m, idx, term in segs:
    L.append('theorem %s : chainTo (150 : ℚ) 2000 %d (%s) [%s] = true := by\n  decide +kernel\n' %
             (name, m, term, ', '.join('c%d' % i for i in idx)))
L.append('end Work.Math.BEH2Data')
open(out, 'w').write('\n'.join(L) + '\n')
print('bracket index', ib, 'cells', n, 'segments', len(segs), [s[0] + ':' + str(s[2][0]) + '-' + str(s[2][-1]) for s in segs], file=sys.stderr)
