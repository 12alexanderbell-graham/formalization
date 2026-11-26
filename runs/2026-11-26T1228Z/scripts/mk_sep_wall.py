#!/usr/bin/env python3
"""Run 2026-11-26T1228Z: write Checked/FSSep/WallSep.lean, the separation stack (SFlow flow and continuity in K,
SUnclamp.start/unclampS/unclampS_neither, SAssemble shooting) ported to the start (0, 1/1000, 0) (a wall moving with
the stream), by asserted replacements; the core takes the two chain coefficients as parameters."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
def rep(s, a, b, n=1):
    assert s.count(a) == n, (a[:80], s.count(a), n); return s.replace(a, b)
fl = (R / 'Checked/FSSep/SFlow.lean').read_text()
un = (R / 'Checked/FSSep/SUnclamp.lean').read_text()
asm = (R / 'Checked/FSSep/SAssemble.lean').read_text()
imports = [l for l in asm.splitlines() if l.startswith('import Mathlib')]
W = '1 / 1000'
f = fl.split('namespace Checked.FSSep.SFlow\nopen Set Checked.FSNeg.NBase Checked.FSSep.SBase\n', 1)[1].split('end Checked.FSSep.SFlow')[0]
f = f[f.index('/-- A solution on [0, T] for every T > 0. -/'):]
def cut(s, start, end):
    i = s.index(start); j = s.index(end, i); return s[:i] + s[j:]
f = cut(f, '/-- Forward uniqueness on [0, T]. -/', 'theorem exists_sol')
f = cut(f, '/-- The field difference between two coefficients', '/-- Continuity of the flow in the coefficient K')
for nm in ('lip', 'cont', 'norm_le', 'unique_right', 'field_diff'):
    f = re.sub(r'(?<![\w.])' + nm + r'(?![\w])', 'Checked.FSSep.SFlow.' + nm, f)
f = rep(f, 'Checked.FSSep.SFlow.norm_le := ', 'norm_le := ')
f = rep(f, 'Y 0 = (0, 0, 0)', f'Y 0 = (0, {W}, 0)', 3)
f = rep(f, '((0 : ℝ), (0 : ℝ), (0 : ℝ))', f'((0 : ℝ), ({W} : ℝ), (0 : ℝ))')
f = rep(f, 'theorem flowK_zero (K : ℝ) : flowK K 0 = (0, 0, 0)', f'theorem flowK_zero (K : ℝ) : flowK K 0 = (0, {W}, 0)')
f = rep(f, '/-- The flow of the clamped coefficient-K field from (0, 0, 0). -/', '/-- The flow of the clamped coefficient-K field from (0, wall velocity, 0). -/')
f = rep(f, 'theorem of_chain {K : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainK K E)', 'theorem of_chain {K : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainKW K E)')
u = un.split('namespace Checked.FSSep.SUnclamp\nopen Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore\n', 1)[1].split('end Checked.FSSep.SUnclamp')[0]
u = u[u.index('/-- The start of a zero-wall-shear trajectory'):]
u = re.sub(r'(?<![\w.])cl_eq(?![\w])', 'Checked.FSSep.SUnclamp.cl_eq', u)
u = re.sub(r'(?<![\w.])q_pos_start(?![\w])', 'Checked.FSSep.SUnclamp.q_pos_start', u)
u = rep(u, '(hp0 : p 0 = 0)', f'(hp0 : p 0 = {W})', 3)
u = rep(u, '-(K * cl (max (0 : ℝ) 0 + 2) (f 0) * cl 2 (q 0)) + 1 - cl 2 (p 0) ^ 2 = 1 := by', '-(K * cl (max (0 : ℝ) 0 + 2) (f 0) * cl 2 (q 0)) + 1 - cl 2 (p 0) ^ 2 = 999999 / 1000000 := by')
u = rep(u, 'exact Checked.FSSep.SUnclamp.q_pos_start h one_pos hq0', 'exact Checked.FSSep.SUnclamp.q_pos_start h (by norm_num) hq0')
u = rep(u, 'have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this', 'have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rw [hp0] at this; linarith', 2)
u = rep(u, 'subst h0; rw [hp0, hq0]; exact ⟨le_rfl, by norm_num, le_rfl, by norm_num, hfs, hfs2⟩', 'subst h0; rw [hp0, hq0]; exact ⟨by norm_num, by norm_num, le_rfl, by norm_num, hfs, hfs2⟩')
a = asm.split('namespace Checked.FSSep.SAssemble\n', 1)[1]
a = a.split('\n', 1)[1]
a = a.split('theorem core_sep')[0]
a = re.sub(r'(?<![\w.])unique_left(?![\w])', 'Checked.FSSep.SFlow.unique_left', a)
a = rep(a, 'Checked.FSSep.SUnclamp.unclampS hK5', 'unclampS hK5')
a = rep(a, 'Checked.FSSep.SUnclamp.unclampS_neither hK', 'unclampS_neither hK')
a = rep(a, '    simpa [flowK_zero] using this', '    simp only [flowK_zero] at this; linarith')
a = rep(a, 'have hP0 : P 0 = 0 := by simp [P, h0]', f'have hP0 : P 0 = {W} := by simp [P, h0]')
core = 'theorem core_sep' + asm.split('theorem core_sep', 1)[1].split('end Checked.FSSep.SAssemble')[0]
core = rep(core, '''theorem core_sep (hO : ChainK (10000000000 / 1988377351) Over)
    (hS : ChainK (10000000000 / 1988377350) SlowS) :
    ∃ β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000)),''',
'''theorem core_sepW {lo hi : ℝ} (hlo5 : 5 ≤ lo) (hlh : lo < hi) (hO : ChainKW lo Over) (hS : ChainKW hi SlowS) :
    ∃ β, -(1 / lo) < β ∧ β < -(1 / hi) ∧''')
core = rep(core, '      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧', '      f 0 = 0 ∧ 0 < p 0 ∧ q 0 = 0 ∧')
core = rep(core, '''  set lo : ℝ := 10000000000 / 1988377351 with hlo
  set hi : ℝ := 10000000000 / 1988377350 with hhi
  have hlh : lo < hi := by rw [hlo, hhi]; norm_num
  have hlo5 : (5 : ℝ) ≤ lo := by rw [hlo]; norm_num
''', '')
core = rep(core, '''  have hβlo : 1 / lo = 1988377351 / 10000000000 := by rw [hlo]; norm_num
  have hβhi : 1 / hi = 1988377350 / 10000000000 := by rw [hhi]; norm_num
  clear_value lo hi
''', '')
core = rep(core, '  have hP0 : P 0 = 0 := by simp [P, flowK_zero]', f'  have hP0 : P 0 = {W} := by simp [P, flowK_zero]')
core = rep(core, '''  refine ⟨-(1 / a), ⟨by rw [hβlo] at hinv1; linarith, by rw [hβhi] at hinv2; linarith⟩,''', '''  refine ⟨-(1 / a), by linarith, by linarith,''')
core = rep(core, 'by simp [hP0], by simp [hQ0],', 'by simp only [zero_div, hP0]; norm_num, by simp [hQ0],')
head = '\n'.join(imports) + '\nimport Checked.FSSep.SFlow\nimport Checked.FSSep.SUnclamp\nimport Checked.FSNeg.NLimit\nimport Checked.FSNeg.NRiccati\nimport Checked.FalknerSkan.FSScale\n'
doc = ('/-! Falkner–Skan separation with the wall moving with the stream: the separation stack (`SFlow`, `SUnclamp`, '
       '`SAssemble`) ported to the start (0, w, 0) of the clamped adverse-sign field, w one thousandth, with the shooting core '
       'taking the two certified chain coefficients as parameters. Written by `runs/2026-11-26T1228Z/scripts/mk_sep_wall.py`. '
       'Module `WallSep`. -/\n')
pre = f'''
/-- The certified chain shape from (0, {W}, 0): every solution of the clamped coefficient-K field on [0, T] from
that start has the event `E`. -/
def ChainKW (K : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →
    Y 0 = (0, {W}, 0) → E Y

'''
out = (head + '\n' + doc + '\nnamespace Checked.FSSep.WallSep\nopen Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase '
       'Checked.FalknerSkan.LimitCore\n' + pre + f + '\n' + u + '\n' + a + '\n' + core + 'end Checked.FSSep.WallSep\n')
(R / 'Checked/FSSep/WallSep.lean').write_text(out)
print('wrote', out.count('\n'), 'lines')
