#!/usr/bin/env python3
"""Run 2026-11-13T0628Z: port the reversed-flow invariance (RInv), unclamping (RUnclamp) and shooting
assembly (RAssemble + RAssembleA) of Checked/FSRev/ to a free shear clamp level Cq ≥ 2, writing
Checked/FSRevW/WInv.lean, WUnclamp.lean, WAssemble.lean. Every replacement must match (asserted)."""
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else '.'


def rd(p):
    return open(f'{ROOT}/{p}').read()


def grab(src, start, end):
    i = src.index(start)
    j = src.index(end, i)
    return src[i:j]


def rep(s, a, b, count=None):
    n = s.count(a)
    assert n > 0, ('no match', a[:90])
    if count is not None:
        assert n == count, ('count', a[:90], n)
    return s.replace(a, b)


def header(src, extra):
    imp = src.split('/-!')[0]
    return imp.rstrip('\n') + '\n' + extra


# ---------------- WInv
R = rd('Checked/FSRev/RInv.lean')
out = header(R, 'import Checked.FSRev.RInv\n\n')
out += """/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five and a shear clamp level at least two: invariance of the lower slow-approach region of the reversed-flow branch. Ported from `Checked/FSRev/RInv.lean` by `runs/2026-11-13T0628Z/scripts/port_wrest.py`. Module `WInv`, run 2026-11-13T0628Z. -/

namespace Checked.FSRevW.WInv
open Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore Checked.FSRev.RInv

theorem clqW {Cq x y : ℝ} (hC : 2 ≤ Cq) (h1 : 1 / 3 < x) (h3 : 0 ≤ y) (h4 : y ≤ 3 * (1 - x)) : cl Cq y = y :=
  cl_of_abs_le (abs_le.2 ⟨by linarith, by linarith⟩)

theorem field_eqW {Cq K s x y z : ℝ} (hC : 2 ≤ Cq) (hs : 0 ≤ s) (h1 : 1 / 3 < y) (h2 : y ≤ 1) (h3 : 0 ≤ z)
    (h4 : z ≤ 3 * (1 - y)) (h5 : 11 / 15 < x) (h6 : x ≤ s + 1) :
    -(K * cl (max s 0 + 2) x * cl Cq z) + 1 - cl 2 y ^ 2 = -(K * x * z) + 1 - y ^ 2 := by
  rw [clf hs h5 h6, clqW hC h1 h3 h4, clp h1 h2]

"""
s = grab(R, 'theorem slow_inv_cl', 'end Checked.FSRev.RInv')
s = rep(s, 'theorem slow_inv_cl {K : ℝ} (hK5 : 5 ≤ K)', 'theorem slow_inv_clW {Cq K : ℝ} (hC : 2 ≤ Cq) (hK5 : 5 ≤ K)')
s = rep(s, 'cl 2 (q η)', 'cl Cq (q η)')
s = rep(s, '(cl_pos two_pos (good x ⟨hx.1.le, hx.2⟩).2.1).le', '(cl_pos (by linarith) (good x ⟨hx.1.le, hx.2⟩).2.1).le')
s = rep(s, 'rwa [field_eq hτpos.le', 'rwa [field_eqW hC hτpos.le')
s = rep(s, 'rwa [clq Cp0 Cq0 Cq3]', 'rwa [clqW hC Cp0 Cq0 Cq3]')
s = rep(s, 'rw [clq c.1 g.2.1.le g.2.2.1.le]', 'rw [clqW hC c.1 g.2.1.le g.2.2.1.le]')
assert 'clq ' not in s and 'field_eq ' not in s
out += s + 'end Checked.FSRevW.WInv\n'
open(f'{ROOT}/Checked/FSRevW/WInv.lean', 'w').write(out)

# ---------------- WUnclamp
U = rd('Checked/FSRev/RUnclamp.lean')
out = header(U, '\n')
out += """/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient and a shear clamp level at least two: a reversed-flow trajectory of the clamped field with neither event never meets a clamp, so it solves the unclamped problem. Ported from `Checked/FSRev/RUnclamp.lean` by `runs/2026-11-13T0628Z/scripts/port_wrest.py`. Module `WUnclamp`, run 2026-11-13T0628Z. -/

namespace Checked.FSRevW.WUnclamp
open Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore

"""
s = grab(U, 'theorem unclamp_from', 'end Checked.FSRev.RUnclamp')
s = rep(s, 'theorem unclamp_from {K : ℝ} (hK : 0 ≤ K)', 'theorem unclamp_fromW {Cq K : ℝ} (hC : 2 ≤ Cq) (hK : 0 ≤ K)')
s = rep(s, 'cl 2 (q η)', 'cl Cq (q η)')
s = rep(s, 'cl 2 (q s)', 'cl Cq (q s)')
s = rep(s, 'rw [cl_eq (by linarith) this.2.le]; exact this.1.le', 'rw [cl_eq (c := Cq) (by linarith) (by linarith [this.2])]; exact this.1.le')
s = rep(s, 'cl_eq (c := 2) (y := q s) (by linarith) c4', 'cl_eq (c := Cq) (y := q s) (by linarith) (by linarith)')
s = rep(s, 'obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eq (by linarith) c4', 'obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eq (c := Cq) (by linarith) (by linarith)')
out += s + 'end Checked.FSRevW.WUnclamp\n'
open(f'{ROOT}/Checked/FSRevW/WUnclamp.lean', 'w').write(out)

# ---------------- WAssemble
A = rd('Checked/FSRev/RAssemble.lean')
AA = rd('Checked/FSRev/RAssembleA.lean')
imp = A.split('/-!')[0]
imp = rep(imp, 'import Checked.FSSep.SFlow\nimport Checked.FSAtt.AAssemble\nimport Checked.FSRev.RBase\nimport Checked.FSRev.RInv\nimport Checked.FSRev.RUnclamp\n',
          'import Checked.FSAtt.AAssemble\nimport Checked.FSRev.RBase\nimport Checked.FSRevW.WFlow\nimport Checked.FSRevW.WInv\nimport Checked.FSRevW.WUnclamp\n')
out = imp + """/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five and a shear clamp level at least two, the shooting argument of the reversed-flow branch with a tube of free end time (at least one): an overshoot chain below, a slow-approach chain above and a tube give a reversed-flow solution in the fast-approach class with its wall value between the two scaled wall values. Ported from `Checked/FSRev/RAssemble.lean` and `Checked/FSRev/RAssembleA.lean` by `runs/2026-11-13T0628Z/scripts/port_wrest.py`. Module `WAssemble`, run 2026-11-13T0628Z. -/

namespace Checked.FSRevW.WAssemble
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSRev.RBase Checked.FalknerSkan.LimitCore
  Checked.FSRevW.WBase Checked.FSRevW.WFlow

"""
s = grab(A, 'theorem slowR_open', 'theorem tube_flow ')
s += grab(AA, 'theorem tube_flowA', 'end Checked.FSRev.RAssembleA')
s = rep(s, 'theorem slowR_open (K α₀ : ℝ)', 'theorem slowR_open (Cq K α₀ : ℝ)')
s = rep(s, 'theorem slowR_not_over {K : ℝ} (hK5 : 5 ≤ K)', 'theorem slowR_not_over {Cq K : ℝ} (hC : 2 ≤ Cq) (hK5 : 5 ≤ K)')
s = rep(s, 'theorem no_touch (K α : ℝ) :', 'theorem no_touch {Cq : ℝ} (hC : 2 ≤ Cq) (K α : ℝ) :')
s = rep(s, 'theorem tube_flowA {K lo hi L α : ℝ} (hT : TubeRA K lo hi L)', 'theorem tube_flowW {Cq K lo hi L α : ℝ} (hT : TubeW Cq K lo hi L)')
s = rep(s, 'theorem neither_classRA {K : ℝ} (hK5 : 5 ≤ K) {L : ℝ} (hL : 1 ≤ L) {lo hi α : ℝ} (hT : TubeRA K lo hi L)',
        'theorem neither_classRW {Cq K : ℝ} (hC : 2 ≤ Cq) (hK5 : 5 ≤ K) {L : ℝ} (hL : 1 ≤ L) {lo hi α : ℝ} (hT : TubeW Cq K lo hi L)')
s = rep(s, 'theorem core_revA {K : ℝ} (hK5 : 5 ≤ K) {L : ℝ} (hL : 1 ≤ L) {lo hi : ℝ} (hlh : lo < hi) (hO : ChainA K lo Over) (hS : ChainA K hi SlowR)\n    (hT : TubeRA K lo hi L) :',
        'theorem core_revW {Cq K : ℝ} (hC : 2 ≤ Cq) (hK5 : 5 ≤ K) {L : ℝ} (hL : 1 ≤ L) {lo hi : ℝ} (hlh : lo < hi)\n    (hO : ChainW Cq K lo Over) (hS : ChainW Cq K hi SlowR) (hT : TubeW Cq K lo hi L) :')
s = rep(s, 'dist_c0 (a', 'Checked.FSAtt.AAssemble.dist_c0 (a')
s = rep(s, 'dist_c1 (a', 'Checked.FSAtt.AAssemble.dist_c1 (a')
s = rep(s, 'dist_c2 (a', 'Checked.FSAtt.AAssemble.dist_c2 (a')
s = rep(s, 'Checked.FSRev.RInv.slow_inv_cl hK5 hF hP hQ', 'Checked.FSRevW.WInv.slow_inv_clW hC hK5 hF hP hQ')
s = rep(s, 'Checked.FSRev.RUnclamp.unclamp_from (by linarith)', 'Checked.FSRevW.WUnclamp.unclamp_fromW hC (by linarith)')
s = rep(s, 'vS K t (Z t)', 'vW Cq K t (Z t)')
s = rep(s, 'vS K t (flowA K α t)', 'vW Cq K t (flowA K α t)')
s = rep(s, 'simp only [hZ, vS]', 'simp only [hZ, vW]')
s = rep(s, 'Checked.FSNeg.NUnclamp.cl_eq (c := 2) (y := 0) (by norm_num) (by norm_num)]',
        'Checked.FSNeg.NUnclamp.cl_eq (c := Cq) (y := 0) (by linarith) (by linarith)]')
s = rep(s, 'Checked.FSSep.SFlow.unique_left', 'Checked.FSRevW.WFlow.unique_left')
s = rep(s, 'no_touch K α', 'no_touch hC K α')
s = rep(s, 'PhiT (fun', 'PhiW Cq (fun')
s = rep(s, '|F η| ≤ η + 2 ∧ |P η| ≤ 2 ∧ |Q η| ≤ 2', '|F η| ≤ η + 2 ∧ |P η| ≤ 2 ∧ |Q η| ≤ Cq')
s = rep(s, 'slowR_not_over hK5', 'slowR_not_over hC hK5')
s = rep(s, 'neither_classRA hK5 hL hT', 'neither_classRW hC hK5 hL hT')
s = rep(s, 'tube_flowA hT hα', 'tube_flowW hT hα')
s = rep(s, 'slowR_open K ', 'slowR_open Cq K ')
s = rep(s, 'over_open K ', 'over_open Cq K ')
s = rep(s, 'flowA_cont K ', 'flowW_cont Cq K ')
s = rep(s, 'cont_comp K ', 'cont_comp Cq K ')
s = rep(s, 'comps K α', 'comps Cq K α')
s = rep(s, 'of_chain hO', 'of_chain hO')
s = re.sub(r'flowA_deriv K ', 'flowW_deriv Cq K ', s)
s = re.sub(r'flowA_zero K ', 'flowW_zero Cq K ', s)
s = rep(s, 'flowA_zero]', 'flowW_zero]')
s = re.sub(r'flowA K ', 'flowW Cq K ', s)
for bad in ['flowA', 'vS ', 'ChainA', 'TubeRA', 'PhiT', 'RAssemble.', 'SFlow.']:
    assert bad not in s, (bad, [l for l in s.split('\n') if bad in l][:3])
out += s + 'end Checked.FSRevW.WAssemble\n'
open(f'{ROOT}/Checked/FSRevW/WAssemble.lean', 'w').write(out)
print('ok')
