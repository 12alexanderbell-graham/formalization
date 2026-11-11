"""Run 2026-11-11T1628Z: rewrite run 1428Z's Checked/Trust/NecessityF.lean (conjunct semantics) into parts
semantics (`necessity% thm i j` = part j of hypothesis i, `Checked.Trust.partsWalk`), adding the redundancy
witnesses of parts 2 (`0 < a t`) and 3 (differentiability) of the flat ΛCDM/CPL laws.
usage: mk_necF_parts.py <NecessityF.lean (conjunct version)> <CosmoParts.lean> <out>"""
import re
import sys

m = open(sys.argv[1]).read()
cp = open(sys.argv[2]).read()
gen = cp[cp.index('/-! Generic redundancy'):cp.index('/-! Witnesses (parts semantics')]


def rep(s, a, b, count=None):
    assert a in s, a
    return s.replace(a, b) if count is None else s.replace(a, b, count)


sec = m[m.index('section Cosmography'):m.index('end Cosmography')]
sec = rep(sec, '_h1_1 :', '_p1_1 :')
sec = rep(sec, '_h1_2 :', '_p1_4 :')
sec = re.sub(r'(_p1_4 : necessity% \S+) 1 2 :=', r'\1 1 4 :=', sec)
sec = rep(sec, 'dS_H_pos, ?_⟩', '⟨dS_H_pos, dS_ev⟩, ?_⟩')
sec = rep(sec, 'theorem dS_H_pos : 0 < hubble Real.exp 0 := by rw [dS_hubble]; norm_num',
          'theorem dS_H_pos : 0 < hubble Real.exp 0 := by rw [dS_hubble]; norm_num\n\n'
          'theorem dS_ev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < Real.exp t ∧ DifferentiableAt ℝ Real.exp t :=\n'
          '  Eventually.of_forall fun t => ⟨Real.exp_pos t, Real.differentiableAt_exp⟩\n')

RED = '''
/-! Parts 2 (`0 < a t` near t₀) and 3 (`a` differentiable near t₀) of the flat ΛCDM/CPL laws are
REDUNDANT: the other parts force them for `a` or for `-a` (`lcdm_noPos`, `cpl_noPos`, `lcdm_noDiff`,
`cpl_noDiff`), and every coefficient is unchanged by `a ↦ -a`. -/
'''
HEADS = [  # (headline, binders before the bundle's drop, args after a t₀, model, extra simp)
    ('Checked.Cosmography.Aviles.flatLCDM_coeffs', 'flatLCDM_coeffs', 'Ω a t₀ hs', 'Ω', 'Ω', '', 'lcdm', 'decel_neg, cosmoCoeff_neg'),
    ('Checked.Cosmography.CPL.flatCPL_coeffs', 'CPL.flatCPL_coeffs', 'Ω w₀ wₐ a t₀ hs', 'Ω w₀ wₐ', 'Ω w₀ wₐ', '', 'cpl', 'decel_neg, cosmoCoeff_neg'),
    ('Checked.Cosmography.CPL.printedL0_ne', 'CPL.printedL0_ne', 'Ω w₀ wₐ a t₀ hs hne', 'Ω w₀ wₐ', 'Ω w₀ wₐ', ' hne', 'cpl', 'cosmoCoeff_neg'),
    ('Checked.Records.F1_l0', 'F1_l0', 'a t₀ hs', '', '', '', 'lcdm', 'cosmoCoeff_neg'),
    ('Checked.Records.F2_toy', 'F2_toy', 'a t₀ hs', '', '', '', 'cpl', 'cosmoCoeff_neg'),
    ('Checked.Records.F2_error', 'F2_error', 'w₀ a t₀ hs', 'w₀', 'w₀', '', 'cpl', 'cosmoCoeff_neg'),
    ('Checked.Records.F3_D4_LCDM', 'F3_D4_LCDM', 'a t₀ hs', '', '', '', 'lcdm', 'decel_neg, cosmoCoeff_neg'),
]
for full, short, intro, pre, _, post, law, simps in HEADS:
    nm = full.split('.')[-1]
    p = (pre + ' ') if pre else ''
    RED += f'''
theorem {nm}_p1_2 : dropped% {full} 1 2 := by
  intro {intro} h
  rcases {law}_noPos h with hL | hL
  · exact {short} {p}a t₀ hL hs{post}
  · simpa only [{simps}] using {short} {p}_ t₀ hL hs.neg{post}

theorem {nm}_p1_3 : dropped% {full} 1 3 := by
  intro {intro} h
  exact {short} {p}a t₀ ({law}_noDiff h) hs{post}
'''
sec = rep(sec, '/-- `0 < H₀` is needed in flat ΛCDM', gen + RED + '\n/-- `0 < H₀` is needed in flat ΛCDM', 1)

chem = m[m.index('section Chemistry'):m.index('end Chemistry')]
chem = rep(chem, '_h4_1 :', '_p4_1 :')
chem = rep(chem, '_h4_2 :', '_p4_2 :')

DUFF = '''section Duffing
open Checked.Sim.Duffing

/-- Duffing: the initial position is needed: the rest state x ≡ 0 solves the equation with v(0) = 0. -/
theorem duffing_first_zero_sol_p1_1 : necessity% Checked.Sim.Duffing.duffing_first_zero_sol 1 1 := by
  refine ⟨fun _ => 0, ⟨fun _ => 0, rfl, fun t _ => ⟨?_, ?_⟩⟩, ?_⟩
  · exact hasDerivWithinAt_const _ _ _
  · simpa using hasDerivWithinAt_const t (Icc (0 : ℝ) (6 / 5)) (0 : ℝ)
  · rintro ⟨h, -⟩; exact lt_irrefl _ (h 0 (by norm_num))

/-- Duffing: the equation for the velocity is needed: x(t) = 1 − 2t², v(t) = −4t has x(0) = 1,
v(0) = 0, x' = v within the interval, and x(1) = −1 < 0. -/
theorem duffing_first_zero_sol_p1_4 : necessity% Checked.Sim.Duffing.duffing_first_zero_sol 1 4 := by
  refine ⟨fun t => 1 - 2 * t ^ 2, ⟨by norm_num, fun t => -4 * t, by norm_num, fun t _ => ?_⟩, ?_⟩
  · have := ((hasDerivAt_pow 2 t).const_mul 2).const_sub 1
    convert this.hasDerivWithinAt using 1; push_cast; ring
  · rintro ⟨h, -⟩; have := h 1 (by norm_num); norm_num at this

'''
out = (m[:m.index('section Cosmography')] + sec + 'end Cosmography\n\n' + chem + 'end Chemistry\n\n' + DUFF
       + 'end Duffing\n\nend Checked.Trust.NCF\n')
out = rep(out, 'import Checked.Sim.Duffing', 'import Checked.Sim.Duffing\nimport Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas')
open(sys.argv[3], 'w').write(out)
print('theorems:', out.count('\ntheorem '))
