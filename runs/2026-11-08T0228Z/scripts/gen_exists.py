"""Cells for the index-2 existence proof: the generator of runs/2026-11-08T0228Z/scripts/gen_len.py
with the grid continued past the zero window to 5, emitted as Work/Math/LE2ExistsData.lean
(chainC checks, T = 5, segments of SEG cells, terminal dummy cell at t = 5)."""
import sys, os
from fractions import Fraction as F
REPO = '/home/claude/formalization'
sys.argv = [sys.argv[0], '2']
sys.path.insert(0, REPO + '/runs/2026-11-08T0228Z/scripts')
import gen_len as G
orig = G.make_grid
def grid():
    g = orig()
    t = g[-1]
    nxt = F(44, 10)
    while nxt <= 5:
        g.append(nxt); nxt += F(1, 10)
    assert g[-1] == 5
    return g
G.make_grid = grid
data = G.run(False)
cells = data['cells']
T = F(5)
SEG = 15
N = 2
def qabs(p, h): return sum(abs(c) * h ** k for k, c in enumerate(p))
for i, c in enumerate(cells):
    t0, h, pt, pp = c['t0'], c['h'], c['pt'], c['pp']
    d1 = G.add(G.deriv(pt), G.sc(-1, pp))
    d2 = G.add(G.mul([t0, F(1)], G.deriv(pp)), G.sc(2, pp), G.mul([t0, F(1)], G.pw(pt, N)))
    K, TH, e, B, d = c['K'], c['TH'], c['eps'], c['B'], c['delta']
    conds = [0 < t0, t0 + h <= T, 0 < h, 1 <= K, 2 / t0 + N * TH ** (N - 1) <= K, K * h < 1, 0 <= d, 0 <= e,
             -(TH - F(1, 100)) <= pt[0] - h * qabs(pt[1:], h), pt[0] + h * qabs(pt[1:], h) <= TH - F(1, 100),
             qabs(d1, h) <= e, qabs(d2, h) <= e * t0,
             d * (1 / (1 - K * h)) + e / K * (1 / (1 - K * h) - 1) <= B, B < F(1, 100),
             TH <= 1, -(1 - F(1, 100)) <= pp[0] - h * qabs(pp[1:], h), pp[0] + h * qabs(pp[1:], h) <= 1 - F(1, 100)]
    assert all(conds), (i, conds)
    if i + 1 < len(cells):
        nx = cells[i + 1]
        assert t0 + h == nx['t0']
        assert abs(G.ev(pt, h) - nx['pt'][0]) + B <= nx['delta'] and abs(G.ev(pp, h) - nx['pp'][0]) + B <= nx['delta'], i
last = cells[-1]
endth, endph = G.ev(last['pt'], last['h']), G.ev(last['pp'], last['h'])
endd = last['B']
print(len(cells), 'cells checked; end at', float(last['t0'] + last['h']), 'theta(5) ~', float(endth), 'B', float(endd), file=sys.stderr)
def q(x):
    x = F(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℚ)"
def ql(p): return '[' + ', '.join(q(x) for x in p) + ']'
o = ["""import Work.Math.LE2ExistsCell

/-! Cells for the index-two existence proof (run 2026-11-08T0228Z): the exact-rational cells of
`runs/2026-11-08T0228Z/scripts/gen_len.py 2` with the grid continued past the first zero to 5,
checked for the clamped flow by kernel evaluation (`chainC`, one declaration per segment); the last
segment links into a terminal cell at t = 5 that only carries the end enclosure. -/

namespace Work.Math.LE2ExistsData
open Set Work.Math.LENCellQ Work.Math.LE2ExistsCell
"""]
for i, c in enumerate(cells):
    o.append(f"def c{i} : Cell := ⟨{q(c['t0'])}, {q(c['h'])}, {q(c['delta'])}, {q(c['eps'])}, {q(c['B'])}, {q(c['TH'])}, {q(c['K'])},\n  {ql(c['pt'])},\n  {ql(c['pp'])}⟩")
nL = len(cells)
o.append(f"def c{nL} : Cell := ⟨(5 : ℚ), (1 : ℚ), {q(endd)}, (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), [{q(endth)}], [{q(endph)}]⟩")
segs = [list(range(k, min(k + SEG, nL))) for k in range(0, nL, SEG)]
for k, sg in enumerate(segs):
    nxt = segs[k + 1][0] if k + 1 < len(segs) else nL
    o.append(f"\ntheorem seg{k}_ok : chainC (5 : ℚ) c{nxt} [{', '.join(f'c{i}' for i in sg)}] = true := by\n  decide +kernel")
c0 = cells[0]
o.append(f"\ntheorem c0_t0 : c0.t0 = {q(c0['t0'])} := rfl\ntheorem c0_δ : c0.δ = {q(c0['delta'])} := rfl\n"
         f"theorem c0_pt : c0.pt.headD 0 = {q(c0['pt'][0])} := rfl\ntheorem c0_pp : c0.pp.headD 0 = {q(c0['pp'][0])} := rfl")
o.append(f"\ntheorem c{nL}_t0 : c{nL}.t0 = 5 := rfl")
for k, sg in enumerate(segs):
    o.append(f"theorem s{k}_t0 : c{sg[0]}.t0 = {q(cells[sg[0]]['t0'])} := rfl")
o.append("\nend Work.Math.LE2ExistsData\n")
open(REPO + '/Work/Math/LE2ExistsData.lean', 'w').write('\n'.join(o))
print('segments', [s[0] for s in segs], 'terminal', nL, file=sys.stderr)
