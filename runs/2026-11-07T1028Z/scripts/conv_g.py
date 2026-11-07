#!/usr/bin/env python3
"""Convert the Gelfand cell certificates (Checked/Math/GCerts{1,2,3}.lean, run 2026-11-06T1228Z) to the
kernel-evaluated form of Checked/Math/GCellQ.lean.

Cells step0..step79 carry the invariant 2 + tφ > 0 (mode false), step80..step91 the invariant φ + tE > 0
(mode true). Every condition is re-checked in exact Fractions, with the defect and invariant polynomials
recomputed, before the Lean files are written: Checked/Math/GQData.lean (cells, one `decide +kernel` per
segment) and Checked/Math/GChain.lean (same statement as before; startI is kept in GCerts.lean).

usage: conv_g.py <repo root> <out GQData.lean> <out GChain.lean> [SEG]
"""
import re
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(sys.argv[1])
OUT = Path(sys.argv[2])
OUTC = Path(sys.argv[3])
SEG = int(sys.argv[4]) if len(sys.argv) > 4 else 15
src = ''.join((ROOT / f'Checked/Math/GCerts{i}.lean').read_text() for i in ('', 1, 2, 3))
T = F(41, 10)
R = r'\((-?\d+(?:/\d+)?) : ℝ\)'


def lst(name):
    m = re.search(r'^def ' + name + r' : List ℚ := \[(.*)\]$', src, re.M)
    return [F(t.strip()) for t in re.findall(r'\(([^()]*?) : ℚ\)', m.group(1))]


steps = sorted(int(k) for k in re.findall(r'^theorem step(\d+) ', src, re.M))
assert steps == list(range(92)), steps[-3:]
cells = []
for k in steps:
    m = re.search(r'have hc := cell pe%d pp%d \(E := fun s => Real.exp \(w s\)\) \(φ := φ\) \(T := 41 / 10\) \(t0 := %s\)\s*\(h := %s\) \(δ := %s\) \(ε := %s\) \(B := %s\) \(EH := %s\) \(PH := %s\)\s*\(K := %s\)'
                  % ((k, k) + (R,) * 8), src, re.S)
    t0, h, d, e, B, EH, PH, K = [F(x) for x in m.groups()]
    cells.append(dict(t0=t0, h=h, d=d, e=e, B=B, EH=EH, PH=PH, K=K, pe=lst('pe%d' % k), pp=lst('pp%d' % k)))
m = re.search(r'theorem step91 [\s\S]*?:\n    \(∀ t ∈ Icc \(3 : ℝ\) %s, 0 < φ t \+ t \* Real.exp \(w t\)\) ∧ \|Real.exp \(w %s\) - %s\| ≤ %s ∧ \|φ %s - %s\| ≤ %s := by' % ((R,) * 7), src)
te, te2, fE, r1, te3, fP, r2 = [F(x) for x in m.groups()]
assert te == te2 == te3 and r1 == r2
r = r1
m = re.search(r'theorem startI [\s\S]*?\(∀ t ∈ Ioc \(0 : ℝ\) \(1/32 : ℝ\), 0 < 2 \+ t \* φ t\) ∧ \|Real.exp \(w \(1/32 : ℝ\)\) - %s\| ≤ %s ∧\s*\|φ \(1/32 : ℝ\) - %s\| ≤ %s' % ((R,) * 4), src)
sE, sr1, sP, sr2 = [F(x) for x in m.groups()]


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
def lo(p, h): return head(p) - h * qabs(p[1:], h)
def hi(p, h): return head(p) + h * qabs(p[1:], h)


def cellprop(c):
    t0, h, d, e, B, EH, PH, K, pe, pp = (c[k] for k in ('t0', 'h', 'd', 'e', 'B', 'EH', 'PH', 'K', 'pe', 'pp'))
    d1 = qsub(qderiv(pe), qmul(pe, pp))
    d2 = qadd(qadd(qmul([t0, F(1)], qderiv(pp)), qsmul(2, pp)), qmul([t0, F(1)], pe))
    return [0 < t0, t0 + h <= T, 0 < h, 1 <= K, PH + EH <= K, 2 / t0 + 1 <= K, K * h < 1, 0 <= d, 0 <= e,
            -(EH - F(1, 100)) <= lo(pe, h), hi(pe, h) <= EH - F(1, 100),
            -(PH - F(1, 100)) <= lo(pp, h), hi(pp, h) <= PH - F(1, 100),
            qabs(d1, h) <= e, qabs(d2, h) <= e * t0,
            d * (1 / (1 - K * h)) + e / K * (1 / (1 - K * h) - 1) <= B, B < F(1, 100)]


def inv(c, mode):
    t0, h, B = c['t0'], c['h'], c['B']
    if not mode:
        return lo(qadd([F(2)], qmul([t0, F(1)], c['pp'])), h) - (t0 + h) * B > 0
    return lo(qadd(c['pp'], qmul([t0, F(1)], c['pe'])), h) - (1 + (t0 + h)) * B > 0


for i, c in enumerate(cells):
    conds = cellprop(c)
    assert all(conds), (i, conds)
    assert inv(c, i >= 80), ('inv', i)
    if i + 1 < len(cells):
        d = cells[i + 1]
        assert c['t0'] + c['h'] == d['t0'], i
        assert abs(qeval(c['pe'], c['h']) - head(d['pe'])) + c['B'] <= d['d'], i
        assert abs(qeval(c['pp'], c['h']) - head(d['pp'])) + c['B'] <= d['d'], i
    else:
        assert c['t0'] + c['h'] == te
        assert abs(qeval(c['pe'], c['h']) - fE) + c['B'] <= r
        assert abs(qeval(c['pp'], c['h']) - fP) + c['B'] <= r
c0 = cells[0]
assert c0['t0'] == F(1, 32) and head(c0['pe']) == sE and head(c0['pp']) == sP and c0['d'] == sr1 == sr2
assert cells[80]['t0'] == 3
print(f'92 cells checked in Fractions (defects and invariants recomputed); end {te}', file=sys.stderr)


def q(x): return f'({x.numerator}/{x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'
def ql(p): return '[' + ', '.join(q(x) for x in p) + ']'
def rr(x): return f'({x.numerator}/{x.denominator} : ℝ)' if x.denominator != 1 else f'({x.numerator} : ℝ)'


out = ["""import Checked.Math.GCellQ

/-! Gelfand problem, `GQData`: the validated cells of the Gelfand chain as data, generated by `runs/2026-11-07T1028Z/scripts/conv_g.py` from the cells of the earlier certificate modules (same Taylor polynomials and cell parameters). Every side condition, every defect bound and the positivity invariant are decided by kernel evaluation over the rationals, one declaration per segment of cells. -/

namespace Checked.Math.GQData
open Set Checked.Math.GCellQ
"""]
for i, c in enumerate(cells):
    out.append(f"def c{i} : Cell := ⟨{q(c['t0'])}, {q(c['h'])}, {q(c['d'])}, {q(c['e'])}, {q(c['B'])}, {q(c['EH'])}, {q(c['PH'])}, {q(c['K'])},\n  {ql(c['pe'])},\n  {ql(c['pp'])}⟩")
X = q(T)
plan = []  # (name, first, last+1, mode, target)
for a, b, mode, tgt in ((0, 80, 'false', 80), (80, 91, 'true', 91)):
    ks = list(range(a, b, SEG))
    for j, s in enumerate(ks):
        e_ = min(s + SEG, b)
        plan.append((f'seg{len(plan)}', s, e_, mode, e_ if e_ < b else tgt))
for name, s, e_, mode, tgt in plan:
    lst_ = '[' + ', '.join(f'c{i}' for i in range(s, e_)) + ']'
    out.append(f"\ntheorem {name}_ok : chainTo {X} {mode} (fun e => linkOK e c{tgt}) {lst_} = true := by\n  decide +kernel")
out.append(f"\ntheorem last_ok : chainTo {X} true (endOK {q(te)} {q(fE)} {q(fP)} {q(r)}) [c91] = true := by\n  decide +kernel")
for i in (0, 80, 91):
    c = cells[i]
    out.append(f"\ntheorem c{i}_t0 : c{i}.t0 = {q(c['t0'])} := rfl\ntheorem c{i}_δ : c{i}.δ = {q(c['d'])} := rfl\n"
               f"theorem c{i}_pe : c{i}.pe.headD 0 = {q(head(c['pe']))} := rfl\ntheorem c{i}_pp : c{i}.pp.headD 0 = {q(head(c['pp']))} := rfl")
out.append("\nend Checked.Math.GQData\n")
OUT.write_text('\n'.join(out))

# GChain: same statement and module doc as before
old = (ROOT / 'Checked/Math/GChain.lean').read_text()
stmt = re.search(r'(/-- Chaining of the start and all cells. -/\ntheorem chain[\s\S]*?:= by)\n', old).group(1)
doc = re.search(r'/-!.*?-/', old, re.S).group(0)
L = []
prevA = 'g0'
for k, (name, s, e_, mode, tgt) in enumerate(plan):
    L.append(f"  obtain ⟨o{k+1}, i{k+1}, a{k+1}, b{k+1}⟩ := seg_q _ _ _ GQData.{name}_ok\n"
             f"    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a{k} b{k}")
    if s == 80:
        L.append("  rw [GQData.c80_t0] at i%d" % (k + 1))
        L.append("  push_cast at i%d" % (k + 1))
        L.append(f"  have h{k+1} := i{k+1}")
    elif mode == 'false':
        L.append(f"  have g{k+1} := ioc_glue g{k} i{k+1}")
    else:
        L.append(f"  have h{k+1} := icc_glue h{k} i{k+1}")
nA = max(k + 1 for k, p in enumerate(plan) if p[3] == 'false')
nB = len(plan)
L.append(f"""  obtain ⟨iE, aE, bE⟩ := end_q _ _ GQData.last_ok
    (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩) (fun t ht => hφ' t ⟨by linarith [ht.1], ht.2⟩) a{nB} b{nB}
  rw [GQData.c80_t0] at g{nA}
  rw [GQData.c91_t0] at h{nB} iE
  have hB := icc_glue h{nB} iE
  rw [GQData.c91_t0, GQData.c91_pe, GQData.c91_δ] at a{nB}
  rw [GQData.c91_t0, GQData.c91_pp, GQData.c91_δ] at b{nB}
  push_cast at g{nA} hB a{nB} b{nB} bE
  refine ⟨fun t ht => g{nA} t ht, fun t ht => hB t ht, a{nB}, b{nB}, bE⟩""")
body = '\n'.join(L)
new = f"""import Checked.Math.GCerts
import Checked.Math.GCellQ
import Checked.Math.GQData

{doc}

namespace Checked.Math.GCerts
open Set Checked.Sim Checked.Math.LECell Checked.Math.GCell Checked.Math.GHelp Checked.Math.GCellQ

{stmt}
  obtain ⟨n0, a0', b0'⟩ := startI hw hφ0 hφ h0
  have hX : ((41/10 : ℚ) : ℝ) = 41 / 10 := by norm_num
  have hE : ∀ t ∈ Icc (0 : ℝ) ((41/10 : ℚ) : ℝ),
      HasDerivWithinAt (fun s => Real.exp (w s)) (Real.exp (w t) * φ t) (Icc 0 ((41/10 : ℚ) : ℝ)) t := by
    rw [hX]; exact fun t ht => exp_sol (hw t ht)
  have hφ' : ∀ t ∈ Ioc (0 : ℝ) ((41/10 : ℚ) : ℝ),
      HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) (Icc 0 ((41/10 : ℚ) : ℝ)) t := by
    rw [hX]; exact hφ
  have p0 : (0 : ℝ) < (GQData.c0.t0 : ℝ) := by rw [GQData.c0_t0]; norm_num
  have a0 : |Real.exp (w (GQData.c0.t0 : ℝ)) - ((GQData.c0.pe.headD 0 : ℚ) : ℝ)| ≤ (GQData.c0.δ : ℝ) := by
    rw [GQData.c0_t0, GQData.c0_pe, GQData.c0_δ]; push_cast; norm_num at a0' ⊢; exact a0'
  have b0 : |φ (GQData.c0.t0 : ℝ) - ((GQData.c0.pp.headD 0 : ℚ) : ℝ)| ≤ (GQData.c0.δ : ℝ) := by
    rw [GQData.c0_t0, GQData.c0_pp, GQData.c0_δ]; push_cast; norm_num at b0' ⊢; exact b0'
  have g0 : ∀ t ∈ Ioc (0 : ℝ) (GQData.c0.t0 : ℝ), Inv false (fun s => Real.exp (w s)) φ t := by
    rw [GQData.c0_t0]; push_cast; norm_num at n0 ⊢; exact n0
{body}

end Checked.Math.GCerts
"""
OUTC.write_text(new)
print('plan:', [(p[0], p[1], p[2], p[3], p[4]) for p in plan], file=sys.stderr)
