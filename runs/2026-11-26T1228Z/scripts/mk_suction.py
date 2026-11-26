#!/usr/bin/env python3
"""Run 2026-11-26T1228Z: write Checked/FSAtt/Suction.lean from AFlow (flow from (C, 0, α)), AUnclamp.unclamp
(f 0 = C with 0 ≤ C ≤ 2: f ≤ t + C keeps the clamp |f| ≤ t + 2) and AAssemble.slow_class, by asserted replacements."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
def rep(s, a, b, n=1):
    assert s.count(a) == n, (a, s.count(a)); return s.replace(a, b)
fl = (R / 'Checked/FSAtt/AFlow.lean').read_text()
un = (R / 'Checked/FSAtt/AUnclamp.lean').read_text()
asm = (R / 'Checked/FSAtt/AAssemble.lean').read_text()
imports = [l for l in fl.splitlines() if l.startswith('import Mathlib')]
# flow
fbody = fl.split('namespace Checked.FSAtt.AFlow\nopen Set Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSSep.SFlow\n', 1)[1]
fbody = fbody.split('/-- Continuity of the flow in α')[0]
fbody = rep(fbody, 'theorem local_sol (K α T : ℝ)', 'theorem local_sol (K C α T : ℝ)')
fbody = rep(fbody, 'theorem exists_sol (K α : ℝ)', 'theorem exists_sol (K C α : ℝ)')
fbody = rep(fbody, 'Y 0 = (0, 0, α)', 'Y 0 = (C, 0, α)', 3)
fbody = rep(fbody, '((0 : ℝ), (0 : ℝ), α)', '(C, (0 : ℝ), α)')
fbody = rep(fbody, 'fun n => local_sol K α _', 'fun n => local_sol K C α _')
fbody = rep(fbody, '/-- The flow of the clamped field from (0, 0, α). -/\nnoncomputable def flowA (K α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol K α)',
            '/-- The flow of the clamped field from (C, 0, α). -/\nnoncomputable def flowC (K C α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol K C α)')
fbody = rep(fbody, 'theorem flowA_zero (K α : ℝ) : flowA K α 0 = (0, 0, α) := (Classical.choose_spec (exists_sol K α)).1',
            'theorem flowC_zero (K C α : ℝ) : flowC K C α 0 = (C, 0, α) := (Classical.choose_spec (exists_sol K C α)).1')
fbody = rep(fbody, 'theorem flowA_deriv (K α : ℝ) :\n    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowA K α) (vS K t (flowA K α t)) (Ici 0) t :=\n  (Classical.choose_spec (exists_sol K α)).2',
            'theorem flowC_deriv (K C α : ℝ) :\n    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowC K C α) (vS K t (flowC K C α t)) (Ici 0) t :=\n  (Classical.choose_spec (exists_sol K C α)).2')
# unclamp (slow part only)
ubody = un.split('namespace Checked.FSAtt.AUnclamp\nopen Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore\n', 1)[1]
ubody = ubody.split('/-- A trajectory of the clamped field from (0, 0, α), 0 < α ≤ 11/10, with p ≤ 1')[0]
ubody = rep(ubody, 'theorem unclamp {K : ℝ} (hK5 : 5 ≤ K) {α : ℝ}', 'theorem unclampC {K : ℝ} (hK5 : 5 ≤ K) {C : ℝ} (hC0 : 0 ≤ C) (hC2 : C ≤ 2) {α : ℝ}')
ubody = rep(ubody, '(hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = α)', '(hf0 : f 0 = C) (hp0 : p 0 = 0) (hq0 : q 0 = α)')
ubody = rep(ubody, '0 ≤ f t ∧ f t ≤ t ∧\n      (η₀ ≤ t', '0 ≤ f t ∧ f t ≤ t + C ∧\n      (η₀ ≤ t')
ubody = rep(ubody, '0 ≤ f s ∧ f s ≤ s) := by', '0 ≤ f s ∧ f s ≤ s + C) := by')
ubody = rep(ubody, 'have hfs : 0 ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hf0] at this',
            'have hfs : 0 ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rw [hf0] at this; linarith')
ubody = rep(ubody, 'have hfs2 : f s ≤ s := by', 'have hfs2 : f s ≤ s + C := by')
# slow class
abody = asm.split('namespace Checked.FSAtt.AAssemble\nopen Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSAtt.ABase Checked.FSAtt.AFlow\n', 1)[1]
abody = abody.split('theorem dist_c0')[0]
abody = rep(abody, 'theorem comps (K α : ℝ) :', 'theorem comps (K C α : ℝ) :')
abody = abody.replace('flowA K α', 'flowC K C α').replace('flowA_deriv K α', 'flowC_deriv K C α').replace('flowA_zero K α', 'flowC_zero K C α')
abody = rep(abody, 'theorem slow_class {K : ℝ} (hK5 : 5 ≤ K) {α : ℝ}', 'theorem slow_classC {K : ℝ} (hK5 : 5 ≤ K) {C : ℝ} (hC0 : 0 ≤ C) (hC2 : C ≤ 2) {α : ℝ}')
abody = rep(abody, '      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = α / Real.sqrt K', '      f 0 = Real.sqrt K * C ∧ p 0 = 0 ∧ q 0 = α / Real.sqrt K')
abody = rep(abody, 'obtain ⟨hF, hP, hQ⟩ := comps K α', 'obtain ⟨hF, hP, hQ⟩ := comps K C α')
abody = rep(abody, 'have hF0 : F 0 = 0 := by simp [F, h0]', 'have hF0 : F 0 = C := by simp [F, h0]')
abody = rep(abody, 'Checked.FSAtt.AUnclamp.unclamp hK5 hα0', 'unclampC hK5 hC0 hC2 hα0')
abody = rep(abody, 'theorem of_chain {K α : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainA K α E) : E (flowC K C α)',
            'theorem of_chainC {K C α : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainC K C α E) : E (flowC K C α)')
head = '\n'.join(imports) + '\nimport Checked.FSSep.SFlow\nimport Checked.FSNeg.NUnclamp\nimport Checked.FSAtt.ABase\nimport Checked.FSAtt.AUnclamp\nimport Checked.FSNeg.NLimit\nimport Checked.FSNeg.NRiccati\nimport Checked.FalknerSkan.FSScale\n'
doc = ('/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five and suction at the wall: the clamped flow from '
       '(C, 0, α), the certified chain shape from that start, and the solution a slow-approach event gives (0 ≤ C ≤ 2 keeps the clamp '
       '|f| ≤ t + 2 inactive). Copies of `AFlow`, `AUnclamp.unclamp` and `AAssemble.slow_class` with the start value C in place of 0; '
       'written by `runs/2026-11-26T1228Z/scripts/mk_suction.py`. Module `Suction`. -/\n')
chain = ('\n/-- The certified chain shape from (C, 0, α): every solution of the clamped coefficient-K field on [0, T] from\n'
         '(C, 0, α) has the event `E`. -/\ndef ChainC (K C α : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=\n'
         '  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →\n    Y 0 = (C, 0, α) → E Y\n')
out = (head + '\n' + doc + '\nnamespace Checked.FSAtt.Suction\nopen Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSSep.SFlow '
       'Checked.FSAtt.ABase Checked.FalknerSkan.LimitCore\n' + chain + fbody + '\n' + re.sub(r'\bcl_eq\b', 'cl_eqC', ubody) + '\n' + abody + '\nend Checked.FSAtt.Suction\n')
out = out.replace('Checked.FSAtt.AUnclamp.cl_eq', 'cl_eqC')
(R / 'Checked/FSAtt/Suction.lean').write_text(out)
print('wrote Checked/FSAtt/Suction.lean', out.count('\n'), 'lines')
