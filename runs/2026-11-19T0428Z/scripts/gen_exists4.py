"""Cells for the index-4 existence proof (run 2026-11-19T0428Z; adapted from
runs/2026-11-08T0228Z/scripts/gen_exists.py, index 2 there).

The cell generator of runs/2026-11-08T0228Z/scripts/gen_len.py with argument 4 (default precision),
started from the singular-start box of Work/Math/LE4Start.lean (its centre and radius at 1/2, so the
first cell links to `Work.Math.LE4ExistsStart.startI` without slack), with the grid continued past
the zero window to 16. Every cell is checked for the clamped flow (the approximations stay a margin
1/100 inside |theta| <= 1, |phi| <= 1), and the result is emitted as Work/Math/LE4ExistsData.lean
(chainC checks, T = 16, segments of SEG cells, terminal dummy cell at t = 16)."""
import sys
from fractions import Fraction as F
REPO = '/home/claude/formalization'
DRY = '--dry' in sys.argv[1:]
sys.argv = [sys.argv[0], '4']
sys.path.insert(0, REPO + '/runs/2026-11-08T0228Z/scripts')
import gen_len as G

T = F(16)
SEG = 15
N = 4
# start box at 1/2 from Work/Math/LE4Start.lean (`startI`)
TH0 = F(38412436093688850163, 40000000000000000000)
PH0 = F(-75623522615201319631, 500000000000000000000)
D0 = F(101099311, 31250000000000000000000000000)
src = open(REPO + '/Work/Math/LE4Start.lean').read()
for s in ['38412436093688850163/40000000000000000000', '-75623522615201319631/500000000000000000000',
          '101099311/31250000000000000000000000000']:
    assert s in src, s

def grid():
    g = G.make_grid()
    assert g[-1] == G.A_HI
    nxt = F(15)
    while nxt <= T:
        g.append(nxt); nxt += F(1, 10)
    assert g[-1] == T
    return g

def run():
    th0, ph0, delta = TH0, PH0, D0
    g = grid()
    cells = []
    for i in range(len(g) - 1):
        t0, h = g[i], g[i + 1] - g[i]
        pt, pp = G.taylor(t0, th0, ph0)
        TH = G.ceil_q(max(abs(G.lowb(pt, h)), abs(G.upb(pt, h))) + G.M + F(1, 10 ** 6), 10 ** 6)
        K = max(F(1), G.ceil_q(2 / t0 + N * TH ** (N - 1), 10 ** 6))
        assert K * h < 1, (i, float(K * h))
        E = 1 / (1 - K * h)
        d1 = G.add(G.deriv(pt), G.sc(-1, pp))
        s = [t0, F(1)]
        d2 = G.add(G.mul(s, G.deriv(pp)), G.sc(2, pp), G.mul(s, G.pw(pt, N)))
        eps = G.ceil_q(max(G.absb(d1, h), G.absb(d2, h) / t0))
        B = G.ceil_q(delta * E + eps / K * (E - 1))
        assert B < G.M, (i, float(B))
        te, pe = G.ev(pt, h), G.ev(pp, h)
        nt, np_ = G.rnd(te, G.SDEN), G.rnd(pe, G.SDEN)
        nd = G.ceil_q(B + max(abs(te - nt), abs(pe - np_)))
        cells.append(dict(t0=t0, h=h, pt=pt, pp=pp, eps=eps, delta=delta, B=B, K=K, TH=TH))
        th0, ph0, delta = nt, np_, nd
    return cells

cells = run()
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
print(len(cells), 'cells checked; end at', float(last['t0'] + last['h']), 'theta(16) ~', float(endth),
      'phi(16) ~', float(endph), 'B', float(endd), file=sys.stderr)
print('max TH', float(max(c['TH'] for c in cells)), 'max |phi| bound',
      float(max(max(abs(c['pp'][0] - c['h'] * qabs(c['pp'][1:], c['h'])), abs(c['pp'][0] + c['h'] * qabs(c['pp'][1:], c['h'])))
                for c in cells)), 'max B', float(max(c['B'] for c in cells)), 'max Kh',
      float(max(c['K'] * c['h'] for c in cells)), file=sys.stderr)
if DRY:
    sys.exit(0)
def q(x):
    x = F(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℚ)"
def ql(p): return '[' + ', '.join(q(x) for x in p) + ']'
o = ["""import Work.Math.LE4ExistsCell

/-! Cells for the index-four existence proof (run 2026-11-19T0428Z): the exact-rational cells of
`runs/2026-11-08T0228Z/scripts/gen_len.py 4` (default precision), started from the singular-start
box of `Work.Math.LE4ExistsStart.startI` at 1/2, with the grid continued past the first zero to 16,
checked for the clamped flow by kernel evaluation (`chainC`, one declaration per segment); the last
segment links into a terminal cell at t = 16 that only carries the end enclosure. Generated by
`runs/2026-11-19T0428Z/scripts/gen_exists4.py` (do not edit by hand). -/

namespace Work.Math.LE4ExistsData
open Set Work.Math.LENCellQ Work.Math.LE4ExistsCell
"""]
for i, c in enumerate(cells):
    o.append(f"def c{i} : Cell := ⟨{q(c['t0'])}, {q(c['h'])}, {q(c['delta'])}, {q(c['eps'])}, {q(c['B'])}, {q(c['TH'])}, {q(c['K'])},\n  {ql(c['pt'])},\n  {ql(c['pp'])}⟩")
nL = len(cells)
o.append(f"def c{nL} : Cell := ⟨(16 : ℚ), (1 : ℚ), {q(endd)}, (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), [{q(endth)}], [{q(endph)}]⟩")
segs = [list(range(k, min(k + SEG, nL))) for k in range(0, nL, SEG)]
for k, sg in enumerate(segs):
    nxt = segs[k + 1][0] if k + 1 < len(segs) else nL
    o.append(f"\ntheorem seg{k}_ok : chainC (16 : ℚ) c{nxt} [{', '.join(f'c{i}' for i in sg)}] = true := by\n  decide +kernel")
c0 = cells[0]
o.append(f"\ntheorem c0_t0 : c0.t0 = {q(c0['t0'])} := rfl\ntheorem c0_δ : c0.δ = {q(c0['delta'])} := rfl\n"
         f"theorem c0_pt : c0.pt.headD 0 = {q(c0['pt'][0])} := rfl\ntheorem c0_pp : c0.pp.headD 0 = {q(c0['pp'][0])} := rfl")
o.append(f"\ntheorem c{nL}_t0 : c{nL}.t0 = 16 := rfl")
for k, sg in enumerate(segs):
    o.append(f"theorem s{k}_t0 : c{sg[0]}.t0 = {q(cells[sg[0]]['t0'])} := rfl")
o.append("\nend Work.Math.LE4ExistsData\n")
open(REPO + '/Work/Math/LE4ExistsData.lean', 'w').write('\n'.join(o))
print('segments', [(s[0], float(cells[s[0]]['t0'])) for s in segs], 'terminal', nL, file=sys.stderr)
