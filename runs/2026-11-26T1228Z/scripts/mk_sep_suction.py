#!/usr/bin/env python3
"""Run 2026-11-26T1228Z: write Checked/FSSep/SuctionSep.lean, the separation stack (SFlow flow and continuity in K,
SUnclamp.start/unclampS/unclampS_neither, SAssemble shooting) ported to the start (cS, 0, 0), cS = 1/1000 (suction),
by asserted replacements; the core takes the two chain coefficients as parameters."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
def rep(s, a, b, n=1):
    assert s.count(a) == n, (a[:80], s.count(a), n); return s.replace(a, b)
fl = (R / 'Checked/FSSep/SFlow.lean').read_text()
un = (R / 'Checked/FSSep/SUnclamp.lean').read_text()
asm = (R / 'Checked/FSSep/SAssemble.lean').read_text()
imports = [l for l in asm.splitlines() if l.startswith('import Mathlib')]
# ---- flow
f = fl.split('namespace Checked.FSSep.SFlow\nopen Set Checked.FSNeg.NBase Checked.FSSep.SBase\n', 1)[1].split('end Checked.FSSep.SFlow')[0]
i = f.index('/-- A solution on [0, T] for every T > 0. -/'); f = f[i:]
# drop the generic lemmas kept in SFlow (uniqueness, field difference): referenced qualified
def cut(s, start, end):
    i = s.index(start); j = s.index(end, i); return s[:i] + s[j:]
f = cut(f, '/-- Forward uniqueness on [0, T]. -/', 'theorem exists_sol')
f = cut(f, '/-- The field difference between two coefficients', '/-- Continuity of the flow in the coefficient K')
for nm in ('lip', 'cont', 'norm_le', 'unique_right', 'field_diff'):
    f = re.sub(r'(?<![\w.])' + nm + r'(?![\w])', 'Checked.FSSep.SFlow.' + nm, f)
f = rep(f, 'Checked.FSSep.SFlow.norm_le := ', 'norm_le := ')  # the structure field keeps its name
f = rep(f, 'Y 0 = (0, 0, 0)', 'Y 0 = (cS, 0, 0)', 3)
f = rep(f, '((0 : ℝ), (0 : ℝ), (0 : ℝ))', '(cS, (0 : ℝ), (0 : ℝ))')
f = rep(f, 'theorem flowK_zero (K : ℝ) : flowK K 0 = (0, 0, 0)', 'theorem flowK_zero (K : ℝ) : flowK K 0 = (cS, 0, 0)')
f = rep(f, '/-- The flow of the clamped coefficient-K field from (0, 0, 0). -/', '/-- The flow of the clamped coefficient-K field from (cS, 0, 0). -/')
f = rep(f, 'theorem of_chain {K : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainK K E)', 'theorem of_chain {K : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainKS K E)')
# ---- unclamp
u = un.split('namespace Checked.FSSep.SUnclamp\nopen Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore\n', 1)[1].split('end Checked.FSSep.SUnclamp')[0]
u = u[u.index('/-- The start of a zero-wall-shear trajectory'):]
u = re.sub(r'(?<![\w.])cl_eq(?![\w])', 'Checked.FSSep.SUnclamp.cl_eq', u)
u = re.sub(r'(?<![\w.])q_pos_start(?![\w])', 'Checked.FSSep.SUnclamp.q_pos_start', u)
u = rep(u, '(hf0 : f 0 = 0)', '(hf0 : f 0 = cS)', 3)
u = rep(u, '0 ≤ f t ∧ f t ≤ t', '0 ≤ f t ∧ f t ≤ t + cS', 2)
u = rep(u, '0 ≤ f s ∧ f s ≤ s)', '0 ≤ f s ∧ f s ≤ s + cS)', 2)
u = rep(u, 'have hfs : 0 ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hf0] at this',
        'have hfs : 0 ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rw [hf0] at this; linarith', 2)
u = rep(u, 'have hfs2 : f s ≤ s := by', 'have hfs2 : f s ≤ s + cS := by', 2)
u = rep(u, '  have h00 : (0 : ℝ) ≤ 0 := le_rfl\n', '  have h00 : (0 : ℝ) ≤ 0 := le_rfl\n  have hcS0 := cS_nonneg\n  have hcS2 := cS_le\n', 2)
# ---- assemble
a = asm.split('namespace Checked.FSSep.SAssemble\n', 1)[1]
a = a.split('\n', 1)[1]  # drop its open line
a = a.split('theorem core_sep')[0]
a = re.sub(r'(?<![\w.])unique_left(?![\w])', 'Checked.FSSep.SFlow.unique_left', a)
a = rep(a, 'Checked.FSSep.SUnclamp.unclampS hK5', 'unclampS hK5')
a = rep(a, 'Checked.FSSep.SUnclamp.unclampS_neither hK', 'unclampS_neither hK')
a = rep(a, '(flowK K t).1 ≤ t ∧', '(flowK K t).1 ≤ t + cS ∧')
a = rep(a, 'have hF0 : F 0 = 0 := by simp [F, h0]', 'have hF0 : F 0 = cS := by simp [F, h0]')
a = rep(a, '  intro F P Q\n', '  intro F P Q\n  have hcS2 := cS_le\n')
core = asm.split('theorem core_sep', 1)[1].split('end Checked.FSSep.SAssemble')[0]
core = 'theorem core_sep' + core
core = rep(core, '''theorem core_sep (hO : ChainK (10000000000 / 1988377351) Over)
    (hS : ChainK (10000000000 / 1988377350) SlowS) :
    ∃ β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000)),''',
'''theorem core_sepS {lo hi : ℝ} (hlo5 : 5 ≤ lo) (hlh : lo < hi) (hO : ChainKS lo Over) (hS : ChainKS hi SlowS) :
    ∃ β, -(1 / lo) < β ∧ β < -(1 / hi) ∧''')
core = rep(core, '      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧', '      0 < f 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧')
core = rep(core, '''  set lo : ℝ := 10000000000 / 1988377351 with hlo
  set hi : ℝ := 10000000000 / 1988377350 with hhi
  have hlh : lo < hi := by rw [hlo, hhi]; norm_num
  have hlo5 : (5 : ℝ) ≤ lo := by rw [hlo]; norm_num
''', '')
core = rep(core, '''  have hβlo : 1 / lo = 1988377351 / 10000000000 := by rw [hlo]; norm_num
  have hβhi : 1 / hi = 1988377350 / 10000000000 := by rw [hhi]; norm_num
  clear_value lo hi
''', '')
core = rep(core, '  have hF0 : F 0 = 0 := by simp [F, flowK_zero]', '  have hF0 : F 0 = cS := by simp [F, flowK_zero]')
core = rep(core, '''  refine ⟨-(1 / a), ⟨by rw [hβlo] at hinv1; linarith, by rw [hβhi] at hinv2; linarith⟩,''',
           '''  refine ⟨-(1 / a), by linarith, by linarith,''')
core = rep(core, 'fun s => Q (s / Real.sqrt a) / Real.sqrt a, A, B, fun s hs => ?_, by simp [hF0],',
           'fun s => Q (s / Real.sqrt a) / Real.sqrt a, A, B, fun s hs => ?_,\n    by simp only [zero_div, hF0]; exact mul_pos hc cS_pos,')
head = '\n'.join(imports) + '\nimport Checked.FSSep.SFlow\nimport Checked.FSSep.SUnclamp\nimport Checked.FSNeg.NLimit\nimport Checked.FSNeg.NRiccati\nimport Checked.FalknerSkan.FSScale\n'
doc = ('/-! Falkner–Skan separation with suction at the wall: the separation stack (`SFlow`, `SUnclamp`, `SAssemble`) '
       'ported to the start (cS, 0, 0) of the clamped adverse-sign field, cS one thousandth (the clamp |f| ≤ t + 2 stays inactive '
       'since f ≤ t + cS), with the shooting core taking the two certified chain coefficients as parameters. Written by '
       '`runs/2026-11-26T1228Z/scripts/mk_sep_suction.py`. Module `SuctionSep`. -/\n')
pre = '''
/-- The suction value of the start, one thousandth. -/
noncomputable def cS : ℝ := 1 / 1000

theorem cS_pos : 0 < cS := by norm_num [cS]
theorem cS_nonneg : 0 ≤ cS := cS_pos.le
theorem cS_le : cS ≤ 2 := by norm_num [cS]

/-- The certified chain shape from (cS, 0, 0): every solution of the clamped coefficient-K field on [0, T] from
(cS, 0, 0) has the event `E`. -/
def ChainKS (K : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →
    Y 0 = (cS, 0, 0) → E Y

'''
out = (head + '\n' + doc + '\nnamespace Checked.FSSep.SuctionSep\nopen Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase '
       'Checked.FalknerSkan.LimitCore\n' + pre + f + '\n' + u + '\n' + a + '\n' + core + 'end Checked.FSSep.SuctionSep\n')
(R / 'Checked/FSSep/SuctionSep.lean').write_text(out)
print('wrote', out.count('\n'), 'lines')
