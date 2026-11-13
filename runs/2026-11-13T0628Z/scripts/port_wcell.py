#!/usr/bin/env python3
"""Run 2026-11-13T0628Z: port the weighted cell lemmas of Checked/FSSep/SCellWC.lean and the reversed-flow
segment lemmas of Checked/FSRev/RCell.lean to a free shear clamp level QC (rational), writing
Checked/FSRevW/WCell.lean. Every replacement must match (asserted). Definitions that do not involve the
clamp (Cell, psdOK, linkOK, side and end conditions, ...) are reused from the original modules."""
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else '.'
S = open(f'{ROOT}/Checked/FSSep/SCellWC.lean').read()
R = open(f'{ROOT}/Checked/FSRev/RCell.lean').read()


def grab(src, start, end):
    i = src.index(start)
    j = src.index(end, i)
    return src[i:j]


def rep(s, a, b, count=None):
    n = s.count(a)
    assert n > 0, ('no match', a[:80])
    if count is not None:
        assert n == count, ('count', a[:80], n)
    return s.replace(a, b)


imports = S.split('/-!')[0].replace('import Checked.FSSep.SBase\n',
                                    'import Checked.FSSep.SBase\nimport Checked.FSSep.SCellWC\nimport Checked.FSRev.RCell\nimport Checked.FSRevW.WBase\n')
out = imports + """/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient and a free shear clamp level: weighted one-sided validated cells of the clamped field, every numeric side condition decided by kernel evaluation over the rationals, and the segment lemmas of the reversed-flow chains. Ported from `Checked/FSSep/SCellWC.lean` and `Checked/FSRev/RCell.lean` by `runs/2026-11-13T0628Z/scripts/port_wcell.py` (the clamp level of the shear component is a parameter; the cell data, side and end conditions are reused). Module `WCell`, run 2026-11-13T0628Z. -/

namespace Checked.FSRevW.WCell
open Set Checked.Sim Checked.Sim.QPoly Checked.Sim.OneSided3 Checked.FSNeg.NBase Checked.FSSep.SBase
  Checked.FSSep.SCellWC Checked.FSRev.RBase Checked.FSRev.RCell Checked.FSRevW.WBase

"""

# ---- CellProp with the clamp level
cp = grab(S, '/-- All hypotheses of the weighted cell step', 'theorem defect3_eval')
cp = rep(cp, 'def CellProp (K T : ℚ) (c : Cell) : Prop :=', 'def CellPropW (K T QC : ℚ) (c : Cell) : Prop :=')
cp = rep(cp, '-2 < qlo c - c.B ∧ qhi c + c.B < 2 ∧ 0 ≤ K', '-QC < qlo c - c.B ∧ qhi c + c.B < QC ∧ 0 ≤ K')
cp = rep(cp, 'instance (K T : ℚ) (c : Cell) : Decidable (CellProp K T c) := by\n  unfold CellProp psdOK; infer_instance',
         'instance (K T QC : ℚ) (c : Cell) : Decidable (CellPropW K T QC c) := by\n  unfold CellPropW psdOK; infer_instance')
cp = rep(cp, 'def cellOK (K T : ℚ) (c : Cell) : Bool := decide (CellProp K T c)', 'def cellOKW (K T QC : ℚ) (c : Cell) : Bool := decide (CellPropW K T QC c)')
cp = rep(cp, '`CellProp` as a Boolean', '`CellPropW` as a Boolean')
cp = rep(cp, 'theorem cellOK_basic {K T : ℚ}', 'theorem cellOKW_basic {K T QC : ℚ}')
cp = rep(cp, 'theorem cell_pos {K T : ℚ}', 'theorem cell_posW {K T QC : ℚ}')
out += cp

sol = grab(S, '/-- The solution hypotheses on [a, T]. -/', '/-- The weighted norm (squared)')
sol = rep(sol, 'def SolC (K T a : ℝ)', 'def SolW (K C T a : ℝ)')
sol = rep(sol, 'cl 2 (q t)', 'cl C (q t)', 2)
sol = rep(sol, 'theorem SolC.mono {K T a b : ℝ} {g p q : ℝ → ℝ} (h : SolC K T a g p q) (hab : a ≤ b) :\n    SolC K T b g p q :=',
          'theorem SolW.mono {K C T a b : ℝ} {g p q : ℝ → ℝ} (h : SolW K C T a g p q) (hab : a ≤ b) :\n    SolW K C T b g p q :=')
out += sol

ca = grab(S, 'set_option maxHeartbeats 1600000 in', '/-- The undershoot side condition')
ca = rep(ca, 'theorem cell_all {K T : ℚ}', 'theorem cell_allW {K T QC : ℚ}')
ca = rep(ca, 'theorem cell_w {K T : ℚ}', 'theorem cell_wW {K T QC : ℚ}')
out += ca

sd = grab(S, 'theorem sideU_spec', '/-- The squared weighted norm')
sd = rep(sd, 'theorem sideU_spec {K T : ℚ}', 'theorem sideU_specW {K T QC : ℚ}')
sd = rep(sd, 'theorem sideO_spec {K T : ℚ}', 'theorem sideO_specW {K T QC : ℚ}')
out += sd

ch = grab(S, '/-- A chain of cells inside [0, T]', 'theorem link_box')
ch = rep(ch, 'def chainS (K T : ℚ) (side term : Cell → Bool) : List Cell → Bool', 'def chainW (K T QC : ℚ) (side term : Cell → Bool) : List Cell → Bool')
ch = rep(ch, 'cellOK K T c && side c && term c', 'cellOKW K T QC c && side c && term c')
ch = rep(ch, 'cellOK K T c && side c && linkOK c d && chainS K T side term (d :: l)', 'cellOKW K T QC c && side c && linkOK c d && chainW K T QC side term (d :: l)')
out += ch

g = grab(S, '/-- A chain from its Boolean check', '/-- Terminal condition of the undershoot chain')
g = rep(g, 'theorem chainS_gen {K T : ℚ}', 'theorem chainW_gen {K T QC : ℚ}')
g = rep(g, 'theorem chainS_head {K T : ℚ}', 'theorem chainW_head {K T QC : ℚ}')
g = rep(g, 'theorem segS_q0 {K T : ℚ}', 'theorem segW_q0 {K T QC : ℚ}')
out += g

e = grab(S, '/-- A final overshoot segment: p(T) > 1 and `Φ` on [c.t0, T]. -/', '/-- The Slow side condition')
e = rep(e, 'theorem endSO_q0 {K T : ℚ}', 'theorem endSOW_q0 {K T QC : ℚ}')
out += e
e2 = grab(S, '/-- A final overshoot segment: p(T) > 1 (no side condition carried). -/', 'end Checked.FSSep.SCellWC')
e2 = rep(e2, 'theorem endO_q0 {K T : ℚ}', 'theorem endOW_q0 {K T QC : ℚ}')
e2 = rep(e2, '(endSO_q0 (Φ', '(endSOW_q0 (Φ')
out += e2

r = grab(R, '/-- Enclosure of the three components on a checked cell. -/', '/-- Side condition p > −1/2 on the cell. -/')
r = rep(r, 'theorem encl {K T : ℚ}', 'theorem enclW {K T QC : ℚ}')
r = rep(r, 'theorem cell_box {K T : ℚ}', 'theorem cell_boxW {K T QC : ℚ}')
r = rep(r, '/-- On a checked cell the enclosed solution lies inside the clamps of `vN`. -/', '/-- On a checked cell the enclosed solution lies inside the clamps of `vW`. -/')
r = rep(r, '∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), |g t| ≤ t + 2 ∧ |p t| ≤ 2 ∧ |q t| ≤ 2 := by', '∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), |g t| ≤ t + 2 ∧ |p t| ≤ 2 ∧ |q t| ≤ (QC : ℝ) := by')
r = rep(r, "have kq1' : ((-2 : ℚ) : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kq1", "have kq1' : ((-QC : ℚ) : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kq1")
r = rep(r, "have kq2' : ((qhi c + c.B : ℚ) : ℝ) < ((2 : ℚ) : ℝ) := by exact_mod_cast kq2", "have kq2' : ((qhi c + c.B : ℚ) : ℝ) < ((QC : ℚ) : ℝ) := by exact_mod_cast kq2")
r = rep(r, 'obtain ⟨b1, b2, b3⟩ := encl c hok hs h0 t ht', 'obtain ⟨b1, b2, b3⟩ := enclW c hok hs h0 t ht')
out += r

sp = grab(R, 'theorem sideP_spec', '/-- End of a tube chain')
sp = rep(sp, 'theorem sideP_spec {K T : ℚ}', 'theorem sideP_specW {K T QC : ℚ}')
sp = rep(sp, '∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), PhiT g p q t := by', '∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), PhiW (QC : ℝ) g p q t := by')
sp = rep(sp, 'refine ⟨cell_box c hok hs h0 t ht, ?_⟩', 'refine ⟨cell_boxW c hok hs h0 t ht, ?_⟩')
sp = rep(sp, 'obtain ⟨-, b2, -⟩ := encl c hok hs h0 t ht', 'obtain ⟨-, b2, -⟩ := enclW c hok hs h0 t ht')
out += sp

ee = grab(R, '/-- The enclosure at the end of a chain ending at `T`. -/', 'end Checked.FSRev.RCell')
ee = rep(ee, 'theorem end_encl {K T : ℚ}', 'theorem end_enclW {K T QC : ℚ}')
ee = rep(ee, 'theorem endT_q0 {K T : ℚ}', 'theorem endTW_q0 {K T QC : ℚ}')
ee = rep(ee, 'theorem endSR_q0 {K T : ℚ}', 'theorem endSRW_q0 {K T QC : ℚ}')
ee = rep(ee, ':= end_encl hside', ':= end_enclW hside')
out += ee

# global renames inside the ported text
for a, b in [('cellOK K T', 'cellOKW K T QC'), ('CellProp K T', 'CellPropW K T QC'),
             ('SolC (K : ℝ) T', 'SolW (K : ℝ) (QC : ℝ) T'), ('chainS K T', 'chainW K T QC'),
             ('cellOK_basic c', 'cellOKW_basic c'),
             ('cell_pos c hok', 'cell_posW c hok'), ('cell_pos e hke', 'cell_posW e hke'),
             ('cell_all c hok', 'cell_allW c hok'), ('cell_w c', 'cell_wW c'),
             ('chainS_gen hside', 'chainW_gen hside'), ('chainS_head c', 'chainW_head c'),

             ('simp only [chainS, Bool.and_eq_true]', 'simp only [chainW, Bool.and_eq_true]')]:
    out = rep(out, a, b)

# the clamp facts inside cell_allW
out = rep(out, "have x5 : (-2 : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kx5", "have x5 : (-(QC : ℝ)) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kx5")
out = rep(out, "have x6 : ((qhi c + c.B : ℚ) : ℝ) < 2 := by exact_mod_cast kx6", "have x6 : ((qhi c + c.B : ℚ) : ℝ) < (QC : ℝ) := by exact_mod_cast kx6")
out = rep(out, """  have cl3 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pq (t - c.t0)| ≤ c.B →
      cl 2 y = y := by""", """  have cl3 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pq (t - c.t0)| ≤ c.B →
      cl (QC : ℝ) y = y := by""")
out = rep(out, "(F2 := fun _ _ _ y3 => cl 2 y3)", "(F2 := fun _ _ _ y3 => cl (QC : ℝ) y3)")
out = rep(out, "(F3 := fun t y1 y2 y3 => -((K : ℝ) * cl (max t 0 + 2) y1 * cl 2 y3) + 1 - cl 2 y2 ^ 2)",
          "(F3 := fun t y1 y2 y3 => -((K : ℝ) * cl (max t 0 + 2) y1 * cl (QC : ℝ) y3) + 1 - cl 2 y2 ^ 2)")
out += 'end Checked.FSRevW.WCell\n'
for bad in ['SolC', 'chainS ', 'cellOK ', 'CellProp ']:
    assert bad not in out, [l for l in out.split('\n') if bad in l][:3]
open(f'{ROOT}/Checked/FSRevW/WCell.lean', 'w').write(out)
print('ok', out.count('\n'))
