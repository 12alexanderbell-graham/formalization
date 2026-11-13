#!/usr/bin/env python3
"""Run 2026-11-13T2028Z: emit Checked/Trust/NecessityY.lean — the wall conditions f(0) = 0 (hypothesis 4)
and p(0) = 0 (hypothesis 5) of the attached-row window headlines are NEEDED, by translates of the
reversed-flow solution of the same row (Checked existence headline's construction, RFlowCells.core_rev_flow),
located by the certified cells of that row's reversed-flow tube.

Exact rational arithmetic only (fractions); every bound is re-checked by the Lean kernel (decide)."""
import re, sys
from fractions import Fraction as Fr
import math

ROOT = sys.argv[1] if len(sys.argv) > 1 else '.'
ROWS = [  # (k, Name, K, window module)
    (13, 'Thirteen', Fr(100, 13), 'NegWallShearRowsTop'),
    (14, 'Fourteen', Fr(50, 7), 'NegWallShearRowsTop'),
    (15, 'Fifteen', Fr(20, 3), 'NegWallShearRowsTop'),
    (16, 'Sixteen', Fr(25, 4), 'NegWallShearRowsTop'),
    (17, 'Seventeen', Fr(100, 17), 'NegWallShearRows'),
    (18, 'Eighteen', Fr(50, 9), 'NegWallShearRows'),
    (19, 'Nineteen', Fr(100, 19), 'NegWallShearRows'),
    # ('1988', '1988', Fr(2500, 497), 'NegWallShear'),  # run 2026-11-13T2028Z: cells of the tube too coarse (q range over one cell wider than the window); needs sub-cell localisation
]

def qeval(p, x):
    r = Fr(0)
    for c in reversed(p):
        r = c + x * r
    return r

def qabs(p, h):
    return qeval([abs(c) for c in p], h)

def parse_cells(src):
    cells = {}
    for m in re.finditer(r'^def c(\d+) : Cell := ⟨(.*)⟩$', src, re.M):
        body = m.group(2)
        nums = [Fr(x) for x in re.findall(r'\((-?\d+(?:/\d+)?) : ℚ\)', body)]
        # 10 scalars then three lists; split lists by bracket structure
        lists = re.findall(r'\[([^\]]*)\]', body)
        L = [[Fr(x) for x in re.findall(r'\((-?\d+(?:/\d+)?) : ℚ\)', l)] for l in lists]
        sc = nums[:10]
        t0, h, d, e, B, mu, w1, w2, r1, r2 = sc
        cells[int(m.group(1))] = dict(t0=t0, h=h, B=B, r1=r1, r2=r2, pg=L[0], pp=L[1], pq=L[2])
    return [cells[i] for i in range(len(cells))]

def bounds(c):
    h = c['h']
    def rng(p, r):
        return p[0] - h * qabs(p[1:], h) - r, p[0] + h * qabs(p[1:], h) + r
    return rng(c['pg'], c['r1']), rng(c['pp'], c['r2']), rng(c['pq'], c['B'])

def crossing(cells, comp):
    """(i, j), i < j: the component is certified negative at the start of cell i and positive at the
    start of cell j (constant Taylor term ± the component radius), with j − i minimal after the dip."""
    rr = 'r2' if comp == 1 else 'r1'
    key = 'pp' if comp == 1 else 'pg'
    seen_neg = None
    for idx, c in enumerate(cells):
        v = c[key][0]
        if v + c[rr] < 0:
            seen_neg = idx
        elif v - c[rr] > 0 and seen_neg is not None:
            return seen_neg, idx
    raise RuntimeError('no crossing')

def qadd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]

def qmul(p, q):
    out = [Fr(0)] * (len(p) + len(q) - 1) if p and q else []
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out

def qshift(p, a):
    res = []
    for c in reversed(p):
        res = qadd([c], qmul([a, Fr(1)], res))
    return res

def slo(p, a, w):
    sp = qshift(p, a)
    return sp[0] - w * qabs(sp[1:], w)

def shi(p, a, w):
    sp = qshift(p, a)
    return sp[0] + w * qabs(sp[1:], w)

def crossing_sub(cells, comp, G=64):
    """(n, a, b): inside cell n, the component is certified negative at σ = a and positive at σ = b = a + h/G."""
    rr = 'r2' if comp == 1 else 'r1'
    key = 'pp' if comp == 1 else 'pg'
    seen_neg = False
    for n, c in enumerate(cells):
        prev = None
        for kk in range(G + 1):
            sg = c['h'] * kk / G
            v = qeval(c[key], sg)
            if v + c[rr] < 0:
                seen_neg = True
                prev = sg
            elif v - c[rr] > 0 and seen_neg and prev is not None:
                return n, prev, sg
            elif v - c[rr] > 0 and seen_neg and prev is None:
                break
    raise RuntimeError('no sub-cell crossing')

def round_down(x, den=1000):
    return Fr(math.floor(x * den), den)

def round_up(x, den=1000):
    return Fr(math.ceil(x * den), den)

def lean_q(x):
    return f'({x.numerator}/{x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'

def lean_r(x):
    return f'({x.numerator} / {x.denominator} : ℝ)' if x.denominator != 1 else f'({x.numerator} : ℝ)'

def seg_of(i):
    return i // 8

def row(k, name, K, wmod):
    tube = open(f'{ROOT}/Checked/FSRev/R{name}Tube.lean').read()
    cells = parse_cells(tube)
    m = re.search(r'\(hα : \|α - \((-?\d+) / (\d+)\)\| ≤ (\d+) / (\d+)\)', tube)
    ctr = Fr(-int(m.group(1)[1:]), int(m.group(2))) if m.group(1).startswith('-') else Fr(int(m.group(1)), int(m.group(2)))
    ctr_txt = f'({m.group(1)} / {m.group(2)})'
    rad_txt = f'{m.group(3)} / {m.group(4)}'
    m2 = re.search(r'theorem tube : TubeR \([^)]*\) \((-?\d+) / (\d+)\) \((-?\d+) / (\d+)\)', tube)
    lo_txt = f'({m2.group(1)} / {m2.group(2)})'; hi_txt = f'({m2.group(3)} / {m2.group(4)})'
    win = open(f'{ROOT}/Checked/FalknerSkan/{wmod}.lean').read()
    wname = 'fs_neg_wall_shear_window' if k == '1988' else f'fs_neg_wall_shear_{k}_window'
    mw = re.search(rf'theorem {wname}[\s\S]*?\n    ([0-9.]+) < q 0 ∧ q 0 < ([0-9.]+) :=', win)
    wlo_txt, whi_txt = mw.group(1), mw.group(2)
    wlo, whi = Fr(wlo_txt), Fr(whi_txt)
    sq = math.sqrt(K.numerator / K.denominator)
    r_lo = round_down(Fr(sq), 10**6) - Fr(1, 10**6); r_hi = round_up(Fr(sq), 10**6) + Fr(1, 10**6)
    assert r_lo ** 2 < K < r_hi ** 2
    out = []
    pre = f'Checked.FSRev.R{name}Tube'
    for comp, tag in ((1, 'p'), (0, 'g')):
        i, j = crossing(cells, comp)
        qs = [bounds(cells[n])[2] for n in range(i, j)]
        qL = round_down(min(q[0] for q in qs)); qU = round_up(max(q[1] for q in qs))
        ok = qL > 0 and ((qU < wlo * r_lo) if comp == 1 else (qL > whi * r_hi))
        if not ok:
            print(f'row {k}: {"p" if comp == 1 else "g"}-crossing cells {i}-{j} do not separate the window '
                  f'(q in [{float(qL)}, {float(qU)}], window*sqrtK in [{float(wlo * r_lo)}, {float(whi * r_hi)}]); skipped',
                  file=sys.stderr)
            continue
        a = cells[i]['t0']; b = cells[j]['t0']
        out.append(dict(tag=tag, comp=comp, i=i, j=j, qL=qL, qU=qU, a=a, b=b))
    return dict(wname=wname, k=k, name=name, K=K, wmod=wmod, cells=cells, ctr_txt=ctr_txt, rad_txt=rad_txt,
                lo_txt=lo_txt, hi_txt=hi_txt, wlo_txt=wlo_txt, whi_txt=whi_txt, r_lo=r_lo, r_hi=r_hi, cr=out, pre=pre)

def emit_cross(R, cr):
    k, pre, K = R['k'], R['pre'], R['K']
    Ktxt = f'{K.numerator}/{K.denominator}'
    Kr = f'({K.numerator} / {K.denominator} : ℝ)'
    tag = cr['tag']; i, j = cr['i'], cr['j']
    compsel = '.2.1' if tag == 'p' else '.1'
    L = []
    L.append(f'''/-- Row {k}: every solution of the clamped field from (0, 0, α), α in the tube's ball, has a zero of
{'p' if tag == 'p' else 'the stream function'} in [{cr['a']}, {cr['b']}] (cells {i}–{j} of `{pre}`) at which {cr['qL']} ≤ q ≤ {cr['qU']}. -/
theorem cross_{tag}_{k} {{Y : ℝ → ℝ × ℝ × ℝ}}
    (hY : ∀ t ∈ Icc (0 : ℝ) (3 / 2 : ℝ), HasDerivWithinAt Y (vS {Kr} t (Y t)) (Icc 0 (3 / 2 : ℝ)) t)
    {{α : ℝ}} (h0 : Y 0 = (0, 0, α)) (hα : |α - {R['ctr_txt']}| ≤ {R['rad_txt']}) :
    ∃ t ∈ Icc {lean_r(cr['a'])} {lean_r(cr['b'])}, (Y t){compsel} = 0 ∧
      {lean_r(cr['qL'])} ≤ (Y t).2.2 ∧ (Y t).2.2 ≤ {lean_r(cr['qU'])} := by
  have hX : (((3/2 : ℚ) : ℚ) : ℝ) = (3 / 2 : ℝ) := by norm_num
  have hK : ((({Ktxt} : ℚ) : ℚ) : ℝ) = {Kr} := by norm_num
  have hs : SolC ((({Ktxt} : ℚ) : ℚ) : ℝ) (((3/2 : ℚ) : ℚ) : ℝ) 0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    rw [hX, hK]
    exact ⟨fun t ht => (hY t ht).fst, fun t ht => (hY t ht).snd.fst, fun t ht => (hY t ht).snd.snd⟩
  have z0 : (({pre}.c0.t0 : ℚ) : ℝ) = 0 := by simp [{pre}.c0]
  have b0 : InBox {pre}.c0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    unfold InBox; simp only [z0, h0]
    simp only [V, {pre}.c0, List.headD_cons]; push_cast
    have hα' := abs_le.1 hα
    nlinarith [hα'.1, hα'.2]''')
    segs = sorted(set(seg_of(n) for n in range(i, j + 1)))
    maxseg = max(segs)
    # boxes at segment starts up to maxseg
    for s in range(1, maxseg + 1):
        nxt = 8 * s
        rest = ', '.join(f'{pre}.c{n}' for n in range(8 * (s - 1) + 1, 8 * s))
        prevbox = 'b0' if s == 1 else f'b{s-1}'
        L.append(f'  obtain ⟨b{s}, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) {pre}.c{nxt} [{rest}] {pre}.c{8*(s-1)} {pre}.seg{s-1}_ok hs {prevbox}')
    for n in range(i, j + 1):
        s = seg_of(n)
        last_cell = (n == j)
        first = 8 * s
        last = min(8 * s + 7, 53)
        rest = ', '.join(f'{pre}.c{m}' for m in range(first + 1, last + 1))
        L.append(f'  obtain ⟨k{n}, x{n}⟩ := chain_box [{rest}] {pre}.c{first} {pre}.seg{s}_ok hs b{s} {pre}.c{n} (by simp)')
        cn = R['cells'][n]
        t0 = cn['t0']; t1 = cn['t0'] + cn['h']
        L.append(f'  have e{n}a : (({pre}.c{n}.t0 : ℚ) : ℝ) = {lean_r(t0)} := by norm_num [{pre}.c{n}]')
        L.append(f'  have e{n}b : (({pre}.c{n}.t0 : ℚ) : ℝ) + (({pre}.c{n}.h : ℚ) : ℝ) = {lean_r(t1)} := by norm_num [{pre}.c{n}]')
        if last_cell:
            continue
        L.append(f'  have B{n} := fun t (ht : t ∈ Icc {lean_r(t0)} {lean_r(t1)}) => cell_bounds {pre}.c{n} k{n} hs x{n} t (by rw [e{n}b, e{n}a]; exact ht)')
        L.append(f'  have nq{n}a := (Rat.cast_le (K := ℝ)).2 (show {lean_q(cr["qL"])} ≤ qlo {pre}.c{n} - {pre}.c{n}.B by decide +kernel)')
        L.append(f'  have nq{n}b := (Rat.cast_le (K := ℝ)).2 (show qhi {pre}.c{n} + {pre}.c{n}.B ≤ {lean_q(cr["qU"])} by decide +kernel)')
        L.append(f'  have nq{n}c : (({lean_q(cr["qL"])} : ℚ) : ℝ) = {lean_r(cr["qL"])} := by norm_num')
        L.append(f'  have nq{n}d : (({lean_q(cr["qU"])} : ℚ) : ℝ) = {lean_r(cr["qU"])} := by norm_num')
    lofn, hifn, rr = ('plo', 'phi', 'r2') if tag == 'p' else ('glo', 'ghi', 'r1')
    hd, rr2 = ('pp', 'r2') if tag == 'p' else ('pg', 'r1')
    L.append(f'  have ni := (Rat.cast_lt (K := ℝ)).2 (show {pre}.c{i}.{hd}.headD 0 + {pre}.c{i}.{rr2} < 0 by decide +kernel)')
    L.append(f'  have nj := (Rat.cast_lt (K := ℝ)).2 (show 0 < {pre}.c{j}.{hd}.headD 0 - {pre}.c{j}.{rr2} by decide +kernel)')
    L.append(f'  rw [Rat.cast_zero] at ni nj')
    a, b = cr['a'], cr['b']
    L.append(f'  have hpa : (Y {lean_r(a)}){compsel} < 0 := by')
    L.append(f'    have := cell_start {pre}.c{i} k{i} hs x{i}')
    L.append(f'    rw [e{i}a] at this')
    L.append(f'    linarith [this.{"2.2.2" if tag == "p" else "2.1"}]')
    L.append(f'  have hpb : 0 < (Y {lean_r(b)}){compsel} := by')
    L.append(f'    have := cell_start {pre}.c{j} k{j} hs x{j}')
    L.append(f'    rw [e{j}a] at this')
    L.append(f'    linarith [this.{"2.2.1" if tag == "p" else "1"}]')
    L.append(f'''  have hcont : ContinuousOn (fun t => (Y t){compsel}) (Icc {lean_r(a)} {lean_r(b)}) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (3 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hY t ht').continuousWithinAt.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).{"snd.fst" if tag == "p" else "fst"}
  obtain ⟨t, ht, hz⟩ := cross (by norm_num) hcont hpa hpb
  refine ⟨t, ht, hz, ?_⟩''')
    # case split over cells i..j
    def case(n, ind):
        return (f'{ind}have c := B{n} t ⟨by linarith, by linarith⟩\n'
                f'{ind}exact ⟨by linarith [c.2.2.2.2.1], by linarith [c.2.2.2.2.2]⟩')
    ns = list(range(i, j))
    L.append('  have ht2 := ht.2; have ht1 := ht.1')
    if len(ns) == 1:
        L.append(case(ns[0], '  '))
    else:
        for idx, n in enumerate(ns):
            cn = R['cells'][n]
            t1 = cn['t0'] + cn['h']
            if idx < len(ns) - 1:
                L.append(f'  rcases le_or_gt t {lean_r(t1)} with h{n} | h{n}')
            L.append('  · ' + case(n, '    ')[4:])
    return '\n'.join(L)

def emit_nec(R):
    k, name, K, pre = R['k'], R['name'], R['K'], R['pre']
    Kr = f'({K.numerator} / {K.denominator} : ℝ)'
    Kd = f'{K.numerator} / {K.denominator}'
    wname = R['wname']
    wthm = f'Checked.FalknerSkan.{R["wmod"]}.{wname}'
    beta = '(-1988 / 10000 : ℝ)' if k == '1988' else f'(-{k} / 100 : ℝ)'
    common = f'''  obtain ⟨a, hla, hah, A, B, C, hlim, hpb, hdec⟩ := core_rev_flow (K := {Kd}) (by norm_num) (by norm_num)
    Checked.FSRev.R{name}Over.chain Checked.FSRev.R{name}Slow.chain Checked.FSRev.R{name}Tube.tube
  have hα : |a - {R['ctr_txt']}| ≤ {R['rad_txt']} := by
    rw [abs_le]; constructor <;> linarith
  have hc : 0 < Real.sqrt {Kr} := Real.sqrt_pos.2 (by norm_num)
  have hβ : (-1 / {Kr}) = {beta} := by norm_num
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 < (flowA {Kr} a (η / Real.sqrt {Kr})).2.1 ∧ (flowA {Kr} a (η / Real.sqrt {Kr})).2.1 < 1 :=
    fun η hη => ⟨by linarith [(hpb η hη).1], (hpb η hη).2⟩'''
    def witness(cr, hidx):
        sel = 'cross_p' if cr['tag'] == 'p' else 'cross_g'
        txt = f'''  obtain ⟨t, ht, hz, hqL, hqU⟩ := {sel}_{k} (flow_sol {Kr} a (3 / 2)) (flowA_zero _ _) hα
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have hs : 0 ≤ Real.sqrt {Kr} * t := mul_nonneg hc.le ht0
  have hst : Real.sqrt {Kr} * t / Real.sqrt {Kr} = t := by field_simp
  have hq0 : 0 < (flowA {Kr} a (Real.sqrt {Kr} * t / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr} := by
    rw [hst]; exact div_pos (by linarith) hc
  have hpos := pos_after (β := -1 / {Kr}) (by norm_num) C hb hs hq0
  have hC : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x => (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr})
      (-((Real.sqrt {Kr} * (flowA {Kr} a ((η + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).1) *
          ((flowA {Kr} a ((η + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr})) -
        {beta} * (1 - (flowA {Kr} a ((η + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.1 ^ 2)) (Ici 0) η := by
    intro η hη
    have := shift_deriv hs C η hη
    rw [hβ] at this
    exact this'''
        return txt
    hs_list = {4: 'A5 B5 C5 D5'}
    parts = []
    # hypothesis 4 (f(0) = 0 dropped): p-crossing
    for cr in R['cr']:
        hidx = 4 if cr['tag'] == 'p' else 5
        notc = (f'''  · rintro ⟨h1, -⟩
    have e : (flowA {Kr} a ((0 + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr} = (flowA {Kr} a t).2.2 / Real.sqrt {Kr} := by
      rw [zero_add, hst]
    beta_reduce at h1
    rw [e] at h1
    have hr : ({lean_r(R['r_lo'])}) < Real.sqrt {Kr} := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    rw [lt_div_iff₀ hc] at h1
    nlinarith''' if hidx == 4 else f'''  · rintro ⟨-, h2⟩
    have e : (flowA {Kr} a ((0 + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr} = (flowA {Kr} a t).2.2 / Real.sqrt {Kr} := by
      rw [zero_add, hst]
    beta_reduce at h2
    rw [e] at h2
    have hr : Real.sqrt {Kr} < ({lean_r(R['r_hi'])}) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    rw [div_lt_iff₀ hc] at h2
    nlinarith''')
        wall = (f'''  · show (flowA {Kr} a ((0 + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.1 = 0
    rw [zero_add, hst]; exact hz''' if hidx == 4 else f'''  · show Real.sqrt {Kr} * (flowA {Kr} a ((0 + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).1 = 0
    rw [zero_add, hst, hz, mul_zero]''')
        what = ('the wall condition f(0) = 0 is needed' if hidx == 4 else 'the wall condition p(0) = 0 is needed')
        how = ('the reversed-flow solution of the same row, translated to the point where its velocity returns to zero (blowing at the wall: f(0) < 0), meets every other hypothesis and has a wall shear below the window'
               if hidx == 4 else
               'the reversed-flow solution of the same row, translated to the point where its stream function returns to zero (a wall moving downstream: p(0) > 0), meets every other hypothesis and has a wall shear above the window')
        refine_mid = ('A\', B\', hC, ?_, shift_lim _ hlim, ?_, shift_dec _ hdec, ?_' if hidx == 4
                      else 'A\', B\', hC, ?_, shift_lim _ hlim, ?_, shift_dec _ hdec, ?_')
        parts.append(f'''/-- In `{wname}`, {what}: {how}. -/
theorem {wname}_h{hidx} : necessity% {wthm} {hidx} := by
{common}
{witness(cr, hidx)}
  have A' := shift_deriv hs A
  have B' := shift_deriv hs B
  refine ⟨fun x => Real.sqrt {Kr} * (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).1,
    fun x => (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.1,
    fun x => (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr},
    {refine_mid}⟩
{wall}
  · intro η hη
    exact hpos (η + Real.sqrt {Kr} * t) (by linarith [mem_Ici.1 hη])
{notc}''')
    return '\n\n'.join(parts)

# ---- β = −0.1988 (sub-cell localisation; run 2026-11-13T2028Z) ----
SUB_ROW = ('1988', '1988', Fr(2500, 497))
SUB_TARGETS = [  # (theorem, kind, L, U): the conclusion forces L ≤ q(0) ≤ U (window: L < q(0) < U)
    ('Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window', 'window', Fr('0.0052181'), Fr('0.0052182')),
    ('Checked.Records.F13_wall_shear', 'rounds', Fr('0.005221') - Fr('0.000003') - Fr(1, 2 * 10**6),
     Fr('0.005221') - Fr('0.000003') + Fr(1, 2 * 10**6)),
]

def sub_row():
    k, name, K = SUB_ROW
    tube = open(f'{ROOT}/Checked/FSRev/R{name}Tube.lean').read()
    cells = parse_cells(tube)
    m = re.search(r'\(hα : \|α - \((-?\d+) / (\d+)\)\| ≤ (\d+) / (\d+)\)', tube)
    ctr_txt = f'({m.group(1)} / {m.group(2)})'; rad_txt = f'{m.group(3)} / {m.group(4)}'
    sq = math.sqrt(K.numerator / K.denominator)
    r_lo = round_down(Fr(sq), 10**6) - Fr(1, 10**6); r_hi = round_up(Fr(sq), 10**6) + Fr(1, 10**6)
    assert r_lo ** 2 < K < r_hi ** 2
    Lmin = min(t[2] for t in SUB_TARGETS); Umax = max(t[3] for t in SUB_TARGETS)
    out = []
    for comp, tag in ((1, 'p'), (0, 'g')):
        n, a, b = crossing_sub(cells, comp)
        c = cells[n]
        qL = round_down(slo(c['pq'], a, b - a) - c['B'], 10**6)
        qU = round_up(shi(c['pq'], a, b - a) + c['B'], 10**6)
        ok = qL > 0 and ((qU < Lmin * r_lo) if comp == 1 else (qL > Umax * r_hi))
        print(f'row {k} sub {tag}: cell {n} σ∈[{a},{b}] q∈[{float(qL)},{float(qU)}] need {"<" if comp==1 else ">"} '
              f'{float(Lmin*r_lo) if comp==1 else float(Umax*r_hi)} ok={ok}', file=sys.stderr)
        if ok:
            out.append(dict(tag=tag, n=n, sa=a, sb=b, qL=qL, qU=qU, t0=c['t0'], h=c['h']))
    return dict(k=k, name=name, K=K, cells=cells, ctr_txt=ctr_txt, rad_txt=rad_txt, r_lo=r_lo, r_hi=r_hi, cr=out,
                pre=f'Checked.FSRev.R{name}Tube')

def emit_cross_sub(R, cr):
    k, pre, K = R['k'], R['pre'], R['K']
    Ktxt = f'{K.numerator}/{K.denominator}'
    Kr = f'({K.numerator} / {K.denominator} : ℝ)'
    tag, n = cr['tag'], cr['n']
    compsel = '.2.1' if tag == 'p' else '.1'
    A = cr['t0'] + cr['sa']; Bv = cr['t0'] + cr['sb']
    sa, sb = lean_q(cr['sa']), lean_q(cr['sb'])
    hd, rr = (f'c{n}.pp', 'r2') if tag == 'p' else (f'c{n}.pg', 'r1')
    L = [f'''/-- Row {k}: every solution of the clamped field from (0, 0, α), α in the tube's ball, has a zero of
{'p' if tag == 'p' else 'the stream function'} in [{A}, {Bv}] (inside cell {n} of `{pre}`) at which {cr['qL']} ≤ q ≤ {cr['qU']}. -/
theorem cross_{tag}_{k} {{Y : ℝ → ℝ × ℝ × ℝ}}
    (hY : ∀ t ∈ Icc (0 : ℝ) (3 / 2 : ℝ), HasDerivWithinAt Y (vS {Kr} t (Y t)) (Icc 0 (3 / 2 : ℝ)) t)
    {{α : ℝ}} (h0 : Y 0 = (0, 0, α)) (hα : |α - {R['ctr_txt']}| ≤ {R['rad_txt']}) :
    ∃ t ∈ Icc {lean_r(A)} {lean_r(Bv)}, (Y t){compsel} = 0 ∧
      {lean_r(cr['qL'])} ≤ (Y t).2.2 ∧ (Y t).2.2 ≤ {lean_r(cr['qU'])} := by
  have hX : (((3/2 : ℚ) : ℚ) : ℝ) = (3 / 2 : ℝ) := by norm_num
  have hK : ((({Ktxt} : ℚ) : ℚ) : ℝ) = {Kr} := by norm_num
  have hs : SolC ((({Ktxt} : ℚ) : ℚ) : ℝ) (((3/2 : ℚ) : ℚ) : ℝ) 0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    rw [hX, hK]
    exact ⟨fun t ht => (hY t ht).fst, fun t ht => (hY t ht).snd.fst, fun t ht => (hY t ht).snd.snd⟩
  have z0 : (({pre}.c0.t0 : ℚ) : ℝ) = 0 := by simp [{pre}.c0]
  have b0 : InBox {pre}.c0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by
    unfold InBox; simp only [z0, h0]
    simp only [V, {pre}.c0, List.headD_cons]; push_cast
    have hα' := abs_le.1 hα
    nlinarith [hα'.1, hα'.2]''']
    sg = seg_of(n)
    for s_ in range(1, sg + 1):
        rest = ', '.join(f'{pre}.c{m}' for m in range(8 * (s_ - 1) + 1, 8 * s_))
        prevbox = 'b0' if s_ == 1 else f'b{s_-1}'
        L.append(f'  obtain ⟨b{s_}, -⟩ := segS_q0 (Φ := PhiT) (fun c hok hsd => sideP_spec c hok hsd) {pre}.c{8*s_} [{rest}] {pre}.c{8*(s_-1)} {pre}.seg{s_-1}_ok hs {prevbox}')
    first = 8 * sg; last = min(8 * sg + 7, 53)
    rest = ', '.join(f'{pre}.c{m}' for m in range(first + 1, last + 1))
    L.append(f'  obtain ⟨kc, xc⟩ := chain_box [{rest}] {pre}.c{first} {pre}.seg{sg}_ok hs b{sg} {pre}.c{n} (by simp)')
    L.append(f'''  have E1 : (({pre}.c{n}.t0 : ℚ) : ℝ) + (({sa} : ℚ) : ℝ) = {lean_r(A)} := by norm_num [{pre}.c{n}]
  have E2 : (({pre}.c{n}.t0 : ℚ) : ℝ) + (({sb} : ℚ) : ℝ) = {lean_r(Bv)} := by norm_num [{pre}.c{n}]
  have hb1 : ({sa} : ℚ) ≤ {pre}.c{n}.h := by decide +kernel
  have hb2 : ({sb} : ℚ) ≤ {pre}.c{n}.h := by decide +kernel
  have SA := sub_bounds {pre}.c{n} kc hs xc {sa} {sa} (by norm_num) le_rfl hb1 {lean_r(A)} (by rw [E1]; exact ⟨le_rfl, le_rfl⟩)
  have SB := sub_bounds {pre}.c{n} kc hs xc {sb} {sb} (by norm_num) le_rfl hb2 {lean_r(Bv)} (by rw [E2]; exact ⟨le_rfl, le_rfl⟩)
  have SQ := fun t (ht : t ∈ Icc {lean_r(A)} {lean_r(Bv)}) => sub_bounds {pre}.c{n} kc hs xc {sa} {sb} (by norm_num) (by norm_num) hb2 t (by rw [E1, E2]; exact ht)
  have ni := (Rat.cast_lt (K := ℝ)).2 (show shi {pre}.{hd} {sa} ({sa} - {sa}) + {pre}.c{n}.{rr} < 0 by decide +kernel)
  have nj := (Rat.cast_lt (K := ℝ)).2 (show 0 < slo {pre}.{hd} {sb} ({sb} - {sb}) - {pre}.c{n}.{rr} by decide +kernel)
  rw [Rat.cast_zero] at ni nj
  have nqa := (Rat.cast_le (K := ℝ)).2 (show {lean_q(cr['qL'])} ≤ slo {pre}.c{n}.pq {sa} ({sb} - {sa}) - {pre}.c{n}.B by decide +kernel)
  have nqb := (Rat.cast_le (K := ℝ)).2 (show shi {pre}.c{n}.pq {sa} ({sb} - {sa}) + {pre}.c{n}.B ≤ {lean_q(cr['qU'])} by decide +kernel)
  have nqc : (({lean_q(cr['qL'])} : ℚ) : ℝ) = {lean_r(cr['qL'])} := by norm_num
  have nqd : (({lean_q(cr['qU'])} : ℚ) : ℝ) = {lean_r(cr['qU'])} := by norm_num
  have hpa : (Y {lean_r(A)}){compsel} < 0 := by
    linarith [SA.{"2.2.2.1" if tag == "p" else "2.1"}]
  have hpb : 0 < (Y {lean_r(Bv)}){compsel} := by
    linarith [SB.{"2.2.1" if tag == "p" else "1"}]
  have hcont : ContinuousOn (fun t => (Y t){compsel}) (Icc {lean_r(A)} {lean_r(Bv)}) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (3 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hY t ht').continuousWithinAt.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).{"snd.fst" if tag == "p" else "fst"}
  obtain ⟨t, ht, hz⟩ := cross (by norm_num) hcont hpa hpb
  refine ⟨t, ht, hz, ?_⟩
  have c := SQ t ht
  exact ⟨by linarith [c.2.2.2.2.1], by linarith [c.2.2.2.2.2]⟩''')
    return '\n'.join(L)

def emit_nec_sub(R):
    k, name, K = R['k'], R['name'], R['K']
    Kr = f'({K.numerator} / {K.denominator} : ℝ)'
    Kd = f'{K.numerator} / {K.denominator}'
    beta = '(-1988 / 10000 : ℝ)'
    parts = []
    for (thm, kind, Lb, Ub) in SUB_TARGETS:
        short = thm.split('.')[-1]
        for cr in R['cr']:
            hidx = 4 if cr['tag'] == 'p' else 5
            if kind == 'window':
                if hidx == 4:
                    close = f'''  · rintro ⟨h1, -⟩
    beta_reduce at h1
    rw [e] at h1
    linarith'''
                else:
                    close = f'''  · rintro ⟨-, h2⟩
    beta_reduce at h2
    rw [e] at h2
    linarith'''
            else:
                close = f'''  · intro h
    unfold Checked.Records.RoundsTo Checked.Records.printedFazioWall at h
    beta_reduce at h
    rw [e, abs_le] at h
    obtain ⟨h1, h2⟩ := h
    have hx' := hx
    generalize (flowA {Kr} a t).2.2 / Real.sqrt {Kr} = x at h1 h2 hx'
    norm_num at h1 h2
    linarith'''
            if hidx == 4:
                hx = f'''  have hr : ({lean_r(R['r_lo'])}) < Real.sqrt {Kr} := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hx : (flowA {Kr} a t).2.2 / Real.sqrt {Kr} < {lean_r(Lb)} := by
    rw [div_lt_iff₀ hc]; nlinarith'''
            else:
                hx = f'''  have hr : Real.sqrt {Kr} < ({lean_r(R['r_hi'])}) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hx : {lean_r(Ub)} < (flowA {Kr} a t).2.2 / Real.sqrt {Kr} := by
    rw [lt_div_iff₀ hc]; nlinarith'''
            wall = (f'''  · show (flowA {Kr} a ((0 + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.1 = 0
    rw [zero_add, hst]; exact hz''' if hidx == 4 else f'''  · show Real.sqrt {Kr} * (flowA {Kr} a ((0 + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).1 = 0
    rw [zero_add, hst, hz, mul_zero]''')
            what = 'the wall condition f(0) = 0 is needed' if hidx == 4 else 'the wall condition p(0) = 0 is needed'
            how = ('the reversed-flow solution at the same β, translated to the point where its velocity returns to zero (f(0) < 0), meets every other hypothesis and has a wall shear below the values the conclusion allows'
                   if hidx == 4 else
                   'the reversed-flow solution at the same β, translated to the point where its stream function returns to zero (p(0) > 0), meets every other hypothesis and has a wall shear above the values the conclusion allows')
            sel = 'cross_p' if cr['tag'] == 'p' else 'cross_g'
            parts.append(f'''/-- In `{short}`, {what}: {how}. -/
theorem {short}_h{hidx} : necessity% {thm} {hidx} := by
  obtain ⟨a, hla, hah, A, B, C, hlim, hpb, hdec⟩ := core_rev_flow (K := {Kd}) (by norm_num) (by norm_num)
    Checked.FSRev.R{name}Over.chain Checked.FSRev.R{name}Slow.chain Checked.FSRev.R{name}Tube.tube
  have hα : |a - {R['ctr_txt']}| ≤ {R['rad_txt']} := by
    rw [abs_le]; constructor <;> linarith
  have hc : 0 < Real.sqrt {Kr} := Real.sqrt_pos.2 (by norm_num)
  have hβ : (-1 / {Kr}) = {beta} := by norm_num
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 < (flowA {Kr} a (η / Real.sqrt {Kr})).2.1 ∧ (flowA {Kr} a (η / Real.sqrt {Kr})).2.1 < 1 :=
    fun η hη => ⟨by linarith [(hpb η hη).1], (hpb η hη).2⟩
  obtain ⟨t, ht, hz, hqL, hqU⟩ := {sel}_{k} (flow_sol {Kr} a (3 / 2)) (flowA_zero _ _) hα
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have hs : 0 ≤ Real.sqrt {Kr} * t := mul_nonneg hc.le ht0
  have hst : Real.sqrt {Kr} * t / Real.sqrt {Kr} = t := by field_simp
  have hq0 : 0 < (flowA {Kr} a (Real.sqrt {Kr} * t / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr} := by
    rw [hst]; exact div_pos (by linarith) hc
  have hpos := pos_after (β := -1 / {Kr}) (by norm_num) C hb hs hq0
  have hC : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x => (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr})
      (-((Real.sqrt {Kr} * (flowA {Kr} a ((η + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).1) *
          ((flowA {Kr} a ((η + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr})) -
        {beta} * (1 - (flowA {Kr} a ((η + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.1 ^ 2)) (Ici 0) η := by
    intro η hη
    have := shift_deriv hs C η hη
    rw [hβ] at this
    exact this
{hx}
  have e : (flowA {Kr} a ((0 + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr} = (flowA {Kr} a t).2.2 / Real.sqrt {Kr} := by
    rw [zero_add, hst]
  have A' := shift_deriv hs A
  have B' := shift_deriv hs B
  refine ⟨fun x => Real.sqrt {Kr} * (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).1,
    fun x => (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.1,
    fun x => (flowA {Kr} a ((x + Real.sqrt {Kr} * t) / Real.sqrt {Kr})).2.2 / Real.sqrt {Kr},
    A', B', hC, ?_, shift_lim _ hlim, ?_, shift_dec _ hdec, ?_⟩
{wall}
  · intro η hη
    exact hpos (η + Real.sqrt {Kr} * t) (by linarith [mem_Ici.1 hη])
{close}''')
    return '\n\n'.join(parts)

def main():
    rows = [row(*r) for r in ROWS]
    head = '''import Checked.FSRev.RFlowCells
import Checked.Trust.NonVacuity
'''
    mods = sorted(set(f'import Checked.FSRev.R{r["name"]}{x}' for r in rows for x in ('Tube', 'Over', 'Slow')))
    mods += sorted(set(f'import Checked.FalknerSkan.{r["wmod"]}' for r in rows))
    SR = sub_row()
    if SR['cr']:
        mods += [f'import Checked.FSRev.R{SR["name"]}{x}' for x in ('Tube', 'Over', 'Slow')]
        mods += ['import Checked.FalknerSkan.NegWallShear', 'import Checked.Records.FalknerSkan']
    body = [head + '\n'.join(mods) + '''

/-! Hypothesis necessity for the attached Falkner–Skan window headlines of the seven decelerating rows read blind,
for the window headline near separation and for the record `F13_wall_shear`: the two wall conditions are needed. Witness: the reversed-flow solution of the same row
(the construction behind the Checked reversed-flow existence headline, `RFlowCells.core_rev_flow`), translated
along the half-line. Its velocity dips below zero and returns; translated to that return point it satisfies
p(0) = 0 with f(0) < 0 (blowing at the wall) and every other hypothesis, and its wall shear lies below the
window. Translated instead to the point where the stream function returns to zero, it satisfies f(0) = 0 with
p(0) > 0 (a wall moving downstream) and every other hypothesis, and its wall shear lies above the window. Both
points and the shear there are located by the certified cells of the row's reversed-flow tube; positivity of the
shear after the translation point follows from the equation (`RFlowCells.pos_after`). Generated by
`runs/2026-11-13T2028Z/scripts/gen_necY.py` (run 2026-11-13T2028Z). -/

namespace Checked.Trust.NCY

open Set Filter Topology Checked.Sim Checked.Sim.QPoly Checked.FSSep.SCellWC Checked.FSNeg.NBase
  Checked.FSSep.SBase Checked.FSAtt.AFlow Checked.FSRev.RBase Checked.FSRev.RCell Checked.FSRev.RFlowCells
''']
    for R in rows:
        for cr in R['cr']:
            body.append(emit_cross(R, cr))
        body.append(emit_nec(R))
        print(R['k'], [(c['tag'], c['i'], c['j'], str(c['qL']), str(c['qU'])) for c in R['cr']], 'sqrtK in', str(R['r_lo']), str(R['r_hi']), file=sys.stderr)
    if SR['cr']:
        for cr in SR['cr']:
            body.append(emit_cross_sub(SR, cr))
        body.append(emit_nec_sub(SR))
    body.append('end Checked.Trust.NCY\n')
    sys.stdout.write('\n\n'.join(body))

main()
