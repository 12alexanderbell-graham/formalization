#!/usr/bin/env python3
"""Run 2026-11-26T0628Z: Checked/FSRev/RAssembleZ.lean from Checked/FSRev/RAssemble.lean by asserted replacements:
neither_classR and core_rev copied with one more conclusion each (q > 0 from the tube's end on, which the proof
already has as `hqpos`), and core_rev's solution named as the scaled flow of the chosen shooting value."""
import re
src = open('Checked/FSRev/RAssemble.lean').read()
def rep(s, a, b, n=1):
    assert s.count(a) == n, (a[:60], s.count(a)); return s.replace(a, b)
imports = src.split('/-!', 1)[0]
nc = 'theorem neither_classR' + src.split('theorem neither_classR', 1)[1].split('theorem core_rev', 1)[0]
cr = 'theorem core_rev' + src.split('theorem core_rev', 1)[1].split('end Checked.FSRev.RAssemble', 1)[0]
nc = rep(nc, 'theorem neither_classR', 'theorem neither_classRZ')
nc = rep(nc, '    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) := by',
            '    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) ∧ (∀ η ∈ Ici (3 / 2 : ℝ), 0 < Q η) := by')
nc = rep(nc, '  refine ⟨tF, tP, tQ, hlim, fun η hη => ⟨hpgt η hη, hplt η hη⟩, ?_⟩\n  exact ',
            '  refine ⟨tF, tP, tQ, hlim, fun η hη => ⟨hpgt η hη, hplt η hη⟩, ?_, hqpos⟩\n  exact ')
cr = rep(cr, 'theorem core_rev', 'theorem core_revZ')
cr = rep(cr, '''    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧''', '''    ∃ a ∈ Icc lo hi, ∃ f p q : ℝ → ℝ,
      (∀ s, f s = Real.sqrt K * (flowA K a (s / Real.sqrt K)).1) ∧
      (∀ s, p s = (flowA K a (s / Real.sqrt K)).2.1) ∧
      (∀ s, q s = (flowA K a (s / Real.sqrt K)).2.2 / Real.sqrt K) ∧
      (∀ s ∈ Ici (3 / 2 * Real.sqrt K), 0 < q s) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧''')
cr = rep(cr, '''  obtain ⟨tF, tP, tQ, hlim, hpb, hdec⟩ :=
    neither_classR hK5''', '''  obtain ⟨tF, tP, tQ, hlim, hpb, hdec, hqp⟩ :=
    neither_classRZ hK5''')
cr = rep(cr, '''  refine ⟨fun s => Real.sqrt K * F (s / Real.sqrt K), fun s => P (s / Real.sqrt K),
    fun s => Q (s / Real.sqrt K) / Real.sqrt K, A, B,''', '''  refine ⟨a, ⟨hloa, ha_lt.le⟩, fun s => Real.sqrt K * F (s / Real.sqrt K), fun s => P (s / Real.sqrt K),
    fun s => Q (s / Real.sqrt K) / Real.sqrt K, fun s => rfl, fun s => rfl, fun s => rfl, fun s hs => ?_, A, B,''')
cr = rep(cr, '''  · refine (C s hs).congr_deriv ?_''', '''  · have hs' : (3 / 2 : ℝ) ≤ s / Real.sqrt K := by rw [le_div_iff₀ hc]; exact hs
    exact div_pos (hqp _ hs') hc
  · refine (C s hs).congr_deriv ?_''')
doc = ('/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five: the shooting argument of '
       '`RAssemble` (an overshoot chain below, a slow-approach chain above and a tube) with two more conclusions, the solution '
       'named as the scaled flow of the chosen shooting value and its second derivative positive from the tube\'s end on. '
       'Generated from `RAssemble` by `runs/2026-11-26T0628Z/scripts/mk_rassemblez.py`. Module `RAssembleZ`, run 2026-11-26T0628Z. -/')
opens = re.search(r'\nopen .*?\n\n', src, re.S).group(0)
out = imports + 'import Checked.FSRev.RAssemble\n\n' + doc + '\n\nnamespace Checked.FSRev.RAssembleZ' + opens.replace('\n\n', ' Checked.FSRev.RAssemble\n\n', 1) + nc + cr + 'end Checked.FSRev.RAssembleZ\n'
open('Checked/FSRev/RAssembleZ.lean', 'w').write(out)
print('ok')
