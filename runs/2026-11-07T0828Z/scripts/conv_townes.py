"""Convert the generated Townes cell certificates of run 2026-11-07T0228Z (TCerts{A,B}*.lean)
into kernel-evaluated chain data (Work.Townes.TCellQ). Reads pt/pp lists and cell parameters
from the existing modules, checks CellProp/linkOK/posOK/negOK in exact Fractions (mirror of the
Lean definitions), and emits Work/Townes/TQData<M>.lean.
Usage: conv_townes.py A|B [ncells]"""
import re, sys
from fractions import Fraction as F

mode = sys.argv[1]
ncut = int(sys.argv[2]) if len(sys.argv) > 2 else None
src = ''.join(open(f'Work/Townes/TCerts{mode}{i}.lean').read() for i in range(1, 6))

def fr(tok):
    tok = tok.strip().strip('()')
    tok = tok.replace(': ℚ', '').replace(': ℝ', '').strip()
    return F(tok)

def lst(name):
    m = re.search(r'^def ' + name + r' : List ℚ := \[(.*)\]$', src, re.M)
    return [fr(t) for t in re.findall(r'\(([^()]*?) : ℚ\)', m.group(1))]

steps = sorted(int(k) for k in re.findall(r'^theorem step(\d+) ', src, re.M))
cells = []
for k in steps:
    m = re.search(r'have hc := cell pt%d pp%d .*?\(T := \((.*?) : ℝ\)\) \(t0 := \((.*?) : ℝ\)\) \(h := \((.*?) : ℝ\)\)\s*\(δ := \((.*?) : ℝ\)\) \(ε := \((.*?) : ℝ\)\) \(B := \((.*?) : ℝ\)\) \(TH := \((.*?) : ℝ\)\) \(K := \((.*?) : ℝ\)\)' % (k, k), src, re.S)
    T, t0, h, d, e, B, TH, K = [F(x) for x in m.groups()]
    cells.append(dict(t0=t0, h=h, d=d, e=e, B=B, TH=TH, K=K, pt=lst('pt%d' % k), pp=lst('pp%d' % k)))
assert T == F(68, 5)
P = lst('P')
m = re.search(r'\(h0 : θ 0 = \((.*?) : ℝ\)\)', src); c0 = F(m.group(1))
m = re.search(r'TStart.start θ φ .*?\(ξ0 := \((.*?) : ℝ\)\) \(η := \((.*?) : ℝ\)\) \(R := \((.*?) : ℝ\)\) \(L := \((.*?) : ℝ\)\) \(Mp := \((.*?) : ℝ\)\)', src, re.S)
xi0, eta, R, L, Mp = [F(x) for x in m.groups()]
# final enclosure: the conclusion of the last step
last = steps[-1]
m = re.search(r'theorem step%d .*?:\s*\n\s*\(∀ t ∈ .*?\) ∧ \|θ \(68/5 : ℝ\) - \((.*?) : ℝ\)\| ≤ \((.*?) : ℝ\) ∧ \|φ \(68/5 : ℝ\) - \((.*?) : ℝ\)\| ≤ \((.*?) : ℝ\)' % last, src, re.S)
fth, r1, fph, r2 = [F(x) for x in m.groups()]
assert r1 == r2
r = r1

def qadd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def qsmul(c, p): return [c * a for a in p]
def qsub(p, q): return qadd(p, qsmul(-1, q))
def qmul(p, q):
    if not p: return []
    return qadd(qsmul(p[0], q), [F(0)] + qmul(p[1:], q))
def qderiv(p):
    if not p: return []
    return qadd(p[1:], [F(0)] + qderiv(p[1:]))
def qeval(p, x):
    v = F(0)
    for c in reversed(p): v = c + x * v
    return v
def qabs(p, h): return qeval([abs(c) for c in p], h)
def head(p): return p[0] if p else F(0)

def cellprop(c):
    t0, h, d, e, B, TH, K, pt, pp = c['t0'], c['h'], c['d'], c['e'], c['B'], c['TH'], c['K'], c['pt'], c['pp']
    d2 = qsub(qadd(qmul([t0, F(1)], qderiv(pp)), pp), qmul([t0, F(1)], qsub(pt, qmul(pt, qmul(pt, pt)))))
    conds = [0 < t0, t0 + h <= T, 0 < h, 1 <= K, 1 / t0 + 1 + 3 * TH * TH <= K, K * h < 1, 0 <= d, 0 <= e,
             -(TH - F(1, 100)) <= head(pt) - h * qabs(pt[1:], h), head(pt) + h * qabs(pt[1:], h) <= TH - F(1, 100),
             qabs(qsub(qderiv(pt), pp), h) <= e, qabs(d2, h) <= e * t0,
             d * (1 / (1 - K * h)) + e / K * (1 / (1 - K * h) - 1) <= B, B < F(1, 100)]
    return conds

pos, neg = (mode == 'A'), (mode == 'B')
if ncut:  # test mode: first ncut cells, final enclosure = end of the cut chain
    cells = cells[:ncut]
    T = cells[-1]['t0'] + cells[-1]['h']
    c = cells[-1]
    fth, fph, r = qeval(c['pt'], c['h']), qeval(c['pp'], c['h']), c['B']
for i, c in enumerate(cells):
    conds = cellprop(c)
    assert all(conds), (i, conds)
    if pos: assert 0 < head(c['pt']) - c['h'] * qabs(c['pt'][1:], c['h']) - c['B'], i
    if neg: assert head(c['pp']) + c['h'] * qabs(c['pp'][1:], c['h']) + c['B'] < 0, i
    if i + 1 < len(cells):
        d = cells[i + 1]
        assert c['t0'] + c['h'] == d['t0'], i
        assert abs(qeval(c['pt'], c['h']) - head(d['pt'])) + c['B'] <= d['d'], i
        assert abs(qeval(c['pp'], c['h']) - head(d['pp'])) + c['B'] <= d['d'], i
    else:
        assert c['t0'] + c['h'] == T
        assert abs(qeval(c['pt'], c['h']) - fth) + c['B'] <= r
        assert abs(qeval(c['pp'], c['h']) - fph) + c['B'] <= r
# start
res = qsub(qderiv([F(0)] + qderiv(P)), qmul([F(0), F(1)], qsub(P, qmul(P, qmul(P, P)))))
C = L * eta + R
c = cells[0]
dP = qderiv(P)
sconds = [0 < xi0, xi0 <= T, head(P) == c0, head(res) == 0, qabs(res[1:], xi0) <= R, qabs(P, xi0) <= Mp,
          1 + 3 * (Mp + eta) ** 2 <= L, 0 < eta, 0 <= R, xi0 * xi0 / 4 * C < eta, c['t0'] == xi0,
          abs(qeval(P, xi0) - head(c['pt'])) + xi0 * xi0 / 4 * C <= c['d'],
          abs(qeval(dP, xi0) - head(c['pp'])) + xi0 / 2 * C <= c['d']]
if pos: sconds.append(0 < head(P) - xi0 * qabs(P[1:], xi0) - xi0 * xi0 / 4 * C)
if neg: sconds += [head(dP) == 0, head(dP[1:]) + xi0 * qabs(dP[2:], xi0) + C / 2 < 0]
assert all(sconds), sconds
print(f'{len(cells)} cells checked in Fractions; final θ ≈ {float(fth):.3e}, φ ≈ {float(fph):.3e}, r = {float(r):.3e}', file=sys.stderr)

def q(x): return f'({x.numerator}/{x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'
def ql(p): return '[' + ', '.join(q(x) for x in p) + ']'
tag = mode + (f'T{ncut}' if ncut else '')
hyps = f'''    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (68/5 : ℝ), HasDerivWithinAt θ (φ ξ) (Icc 0 (68/5 : ℝ)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (68/5 : ℝ)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (68/5 : ℝ), HasDerivWithinAt φ (-(1 / ξ * φ ξ) + θ ξ - θ ξ ^ 3) (Icc 0 (68/5 : ℝ)) ξ)
    (h0 : θ 0 = ({c0.numerator}/{c0.denominator} : ℝ))'''
if ncut:
    final = ''
else:
    concl = '(∀ t ∈ Icc (0 : ℝ) (68/5 : ℝ), 0 < θ t) ∧ 0 < φ (68/5 : ℝ)' if pos else '(∀ t ∈ Ioc (0 : ℝ) (68/5 : ℝ), φ t < 0) ∧ θ (68/5 : ℝ) < 0'
    fin = ('  refine ⟨k.1 rfl, ?_⟩\n  have e := abs_le.1 k.2.2.2\n  have n : (0 : ℝ) < ' + f'({fph.numerator}/{fph.denominator} : ℝ) - ({r.numerator}/{r.denominator} : ℝ) := by norm_num\n  linarith [e.1]') if pos else \
          ('  refine ⟨k.2.1 rfl, ?_⟩\n  have e := abs_le.1 k.2.2.1\n  have n : ' + f'({fth.numerator}/{fth.denominator} : ℝ) + ({r.numerator}/{r.denominator} : ℝ) < 0 := by norm_num\n  linarith [e.2]')
    final = f'''
/-- Same statement as `Work.Townes.TCerts{mode}.chain`, from the kernel-evaluated check. -/
theorem chain {{θ φ : ℝ → ℝ}}
{hyps} :
    {concl} := by
  have k := shoot_q start cells shoot_ok (θ := θ) (φ := φ) (by push_cast; exact hθ)
    (by push_cast; exact hφ0) (by push_cast; exact hφ) (by push_cast; exact h0)
  push_cast at k
{fin}
'''
SEG = int(__import__('os').environ.get('SEG', '25'))
n = len(cells)
segs = [list(range(k, min(k + SEG, n))) for k in range(0, n, SEG)]
B = lambda b: str(b).lower()
out = [f"""import Work.Townes.TCellQ

/-! Generated by `runs/2026-11-07T0828Z/scripts/conv_townes.py {mode}` (SEG = {SEG}) from the cells of
`Work/Townes/TCerts{mode}1–5.lean` (run 2026-11-07T0228Z; same series, Taylor polynomials and
parameters). Every numeric side condition and every defect bound is checked by kernel evaluation
over ℚ (`decide +kernel`), one declaration per segment of {SEG} cells. -/

namespace Work.Townes.TQData{tag}
open Set Work.Townes.TCellQ

/-- The singular start (degree-{len(P)-1} series on [0, {xi0}]). -/
def start : Start := ⟨{q(xi0)}, {q(eta)}, {q(R)}, {q(L)}, {q(Mp)},
  {ql(P)}⟩
"""]
for i, c in enumerate(cells):
    out.append(f"def c{i} : Cell := ⟨{q(c['t0'])}, {q(c['h'])}, {q(c['d'])}, {q(c['e'])}, {q(c['B'])}, {q(c['TH'])}, {q(c['K'])},\n  {ql(c['pt'])},\n  {ql(c['pp'])}⟩")
X = q(T)
out.append(f"\ntheorem start_ok : decide (StartProp {X} {q(c0)} {B(pos)} {B(neg)} start c0) = true := by\n  decide +kernel\n")
for k, sg in enumerate(segs):
    lst_ = '[' + ', '.join(f'c{i}' for i in sg) + ']'
    if k + 1 < len(segs):
        out.append(f"theorem seg{k}_ok : segOK {X} {B(pos)} {B(neg)} c{segs[k+1][0]} {lst_} = true := by\n  decide +kernel\n")
    else:
        out.append(f"theorem seg{k}_ok : chainOK {X} {B(pos)} {B(neg)} {q(fth)} {q(fph)} {q(r)} {lst_} = true := by\n  decide +kernel\n")
if not ncut:
    concl = '(∀ t ∈ Icc (0 : ℝ) (68/5 : ℝ), 0 < θ t) ∧ 0 < φ (68/5 : ℝ)' if pos else '(∀ t ∈ Ioc (0 : ℝ) (68/5 : ℝ), φ t < 0) ∧ θ (68/5 : ℝ) < 0'
    L_ = [f"""/-- Same statement as `Work.Townes.TCerts{mode}.chain`, from the kernel-evaluated checks. -/
theorem chain {{θ φ : ℝ → ℝ}}
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (68/5 : ℝ), HasDerivWithinAt θ (φ ξ) (Icc 0 (68/5 : ℝ)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (68/5 : ℝ)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (68/5 : ℝ), HasDerivWithinAt φ (-(1 / ξ * φ ξ) + θ ξ - θ ξ ^ 3) (Icc 0 (68/5 : ℝ)) ξ)
    (h0 : θ 0 = ({c0.numerator}/{c0.denominator} : ℝ)) :
    {concl} := by
  have hX : (({X}) : ℝ) = 68/5 := by norm_num
  have hθ' : ∀ ξ ∈ Icc (0 : ℝ) (({X}) : ℝ), HasDerivWithinAt θ (φ ξ) (Icc 0 (({X}) : ℝ)) ξ := by
    rw [hX]; exact hθ
  have hφ0' : ContinuousWithinAt φ (Icc 0 (({X}) : ℝ)) 0 := by rw [hX]; exact hφ0
  have hφ' : ∀ ξ ∈ Ioc (0 : ℝ) (({X}) : ℝ),
      HasDerivWithinAt φ (-(1 / ξ * φ ξ) + θ ξ - θ ξ ^ 3) (Icc 0 (({X}) : ℝ)) ξ := by
    rw [hX]; exact hφ
  have h0' : θ 0 = (({q(c0)}) : ℝ) := by rw [h0]; norm_num
  obtain ⟨-, p0, sp0, sn0, a0, b0⟩ := start_q start c0 start_ok hθ' hφ0' hφ' h0'"""]
    for k, sg in enumerate(segs):
        h = f'c{sg[0]}'
        tl = '[' + ', '.join(f'c{i}' for i in sg[1:]) + ']'
        if k + 1 < len(segs):
            nx = f'c{segs[k+1][0]}'
            L_.append(f"""  obtain ⟨o{k+1}, sp{k+1}, sn{k+1}, a{k+1}, b{k+1}⟩ := seg_q {nx} {tl} {h} seg{k}_ok
    (fun t ht => hθ' t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a{k} b{k}""")
        else:
            L_.append(f"""  obtain ⟨spE, snE, fθ, fφ⟩ := chain_q {tl} {h} seg{k}_ok
    (fun t ht => hθ' t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a{k} b{k}""")
    m = len(segs)
    if pos:
        g = 'spE rfl'
        for k in range(m - 1, 0, -1): g = f'icc_glue (sp{k} rfl) ({g})'
        g = f'icc_glue (sp0 rfl) ({g})'
        L_.append(f"  rw [hX] at fφ\n  refine ⟨hX ▸ {g}, ?_⟩\n  have e := abs_le.1 fφ\n  have n : (0 : ℝ) < ({fph.numerator}/{fph.denominator} : ℝ) - ({r.numerator}/{r.denominator} : ℝ) := by norm_num\n  push_cast at e\n  linarith [e.1]")
    else:
        g = 'snE rfl'
        for k in range(m - 1, 0, -1): g = f'icc_glue (sn{k} rfl) ({g})'
        g = f'ioc_glue (sn0 rfl) ({g})'
        L_.append(f"  rw [hX] at fθ\n  refine ⟨hX ▸ {g}, ?_⟩\n  have e := abs_le.1 fθ\n  have n : ({fth.numerator}/{fth.denominator} : ℝ) + ({r.numerator}/{r.denominator} : ℝ) < 0 := by norm_num\n  push_cast at e\n  linarith [e.2]")
    out.append('\n'.join(L_) + '\n')
out.append(f"end Work.Townes.TQData{tag}\n")
open(f'Work/Townes/TQData{tag}.lean', 'w').write('\n'.join(out))
