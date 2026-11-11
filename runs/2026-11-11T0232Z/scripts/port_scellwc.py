#!/usr/bin/env python3
"""Run 2026-11-11T0232Z: port Work/FSNeg/NCellWC.lean (coefficient 10) to Work/FSSep/SCellWC.lean (rational
coefficient K, field Work.FSSep.SBase.vS, Slow threshold 11/15). Every replacement must match."""
src = open('Work/FSNeg/NCellWC.lean').read()
s = src
def rep(old, new, count=None):
    global s
    n = s.count(old)
    assert n > 0, (old,)
    if count is not None: assert n == count, (old, n)
    s = s.replace(old, new)
i = s.index('/-!'); j = s.index('-/', i) + 2
s = s[:i] + '''/-!
# Falkner–Skan separation, scaled adverse-sign field with a rational coefficient K: weighted one-sided cells for the CLAMPED field `Work.FSSep.SBase.vS K` (run 2026-11-11T0232Z)

Port of `Work.FSNeg.NCellWC` (coefficient 10) with the coefficient replaced by a rational
parameter `K` (`CellProp K T c` also checks 0 ≤ K, used for the sign of the lower bounds
K·m ≤ K·y1 and K·q). The one-sided bound `os_neg` is stated for a real K. Chains carry the side
condition p < 1 only (`sideU`; q(0) = 0 at a zero wall shear, so no sign condition on q) and end in
the region 0 ≤ p, q < 3(1 − p), g > 11/15 (`endSl`, `endSl_q0`) or above p = 1 (`endO`, `endO_q0`).
Generator `runs/2026-11-11T0232Z/scripts/gen_sep_wc.py`, emitter `emit_sep_wc.py`, port script
`port_scellwc.py`.
-/''' + s[j:]
rep('import Work.FSNeg.NBase', 'import Work.FSSep.SBase')
rep('namespace Work.FSNeg.NCellWC', 'namespace Work.FSSep.SCellWC')
rep('end Work.FSNeg.NCellWC', 'end Work.FSSep.SCellWC')
rep('open Set Checked.Sim Checked.Sim.QPoly Work.Sim.OneSided3 Work.FSNeg.NBase',
    'open Set Checked.Sim Checked.Sim.QPoly Work.Sim.OneSided3 Work.FSNeg.NBase Work.FSSep.SBase')
rep('/-- The third defect pq′ + 10·pg·pq − 1 + pp². -/\ndef defect3 (c : Cell) : List ℚ :=\n  qadd (qsub (qadd (qderiv c.pq) (qmul (qsmul 10 c.pg) c.pq)) [1]) (qmul c.pp c.pp)',
    '/-- The third defect pq′ + K·pg·pq − 1 + pp². -/\ndef defect3 (K : ℚ) (c : Cell) : List ℚ :=\n  qadd (qsub (qadd (qderiv c.pq) (qmul (qsmul K c.pg) c.pq)) [1]) (qmul c.pp c.pp)')
rep('def CellProp (T : ℚ) (c : Cell) : Prop :=', 'def CellProp (K T : ℚ) (c : Cell) : Prop :=')
rep('+ qabs (defect3 c) c.h ^ 2 < c.ε ^ 2 ∧', '+ qabs (defect3 K c) c.h ^ 2 < c.ε ^ 2 ∧')
rep('(10 * mlo c)', '(K * mlo c)', 4)
rep('(10 * qlo c) (', '(K * qlo c) (', 2)
rep('(10 * qhi c) (', '(K * qhi c) (', 2)
rep('  -2 < qlo c - c.B ∧ qhi c + c.B < 2\n', '  -2 < qlo c - c.B ∧ qhi c + c.B < 2 ∧ 0 ≤ K\n')
rep('instance (T : ℚ) (c : Cell) : Decidable (CellProp T c) := by', 'instance (K T : ℚ) (c : Cell) : Decidable (CellProp K T c) := by')
rep('def cellOK (T : ℚ) (c : Cell) : Bool := decide (CellProp T c)', 'def cellOK (K T : ℚ) (c : Cell) : Bool := decide (CellProp K T c)')
rep('def chainS (T : ℚ) (side term : Cell → Bool) : List Cell → Bool\n  | [] => false\n  | [c] => cellOK T c && side c && term c\n  | c :: d :: l => cellOK T c && side c && linkOK c d && chainS T side term (d :: l)',
    'def chainS (K T : ℚ) (side term : Cell → Bool) : List Cell → Bool\n  | [] => false\n  | [c] => cellOK K T c && side c && term c\n  | c :: d :: l => cellOK K T c && side c && linkOK c d && chainS K T side term (d :: l)')
rep('{T : ℚ}', '{K T : ℚ}')
rep('cellOK T ', 'cellOK K T ')
rep('CellProp T ', 'CellProp K T ')
rep('chainS T ', 'chainS K T ')
rep('theorem defect3_eval (c : Cell) (σ : ℝ) :\n    dEvalQ c.pq σ + 10 * evalQ c.pg σ * evalQ c.pq σ - 1 + evalQ c.pp σ ^ 2 = evalQ (defect3 c) σ := by',
    'theorem defect3_eval (K : ℚ) (c : Cell) (σ : ℝ) :\n    dEvalQ c.pq σ + (K : ℝ) * evalQ c.pg σ * evalQ c.pq σ - 1 + evalQ c.pp σ ^ 2 = evalQ (defect3 K c) σ := by')
rep('def SolC (T a : ℝ) (g p q : ℝ → ℝ) : Prop :=', 'def SolC (K T a : ℝ) (g p q : ℝ → ℝ) : Prop :=')
rep('HasDerivWithinAt q (-(10 * cl (max t 0 + 2) (g t) * cl 2 (q t)) + 1 - cl 2 (p t) ^ 2)\n    (Icc 0 T) t)',
    'HasDerivWithinAt q (-(K * cl (max t 0 + 2) (g t) * cl 2 (q t)) + 1 - cl 2 (p t) ^ 2)\n    (Icc 0 T) t)')
rep('theorem SolC.mono {T a b : ℝ} {g p q : ℝ → ℝ} (h : SolC T a g p q) (hab : a ≤ b) :\n    SolC T b g p q :=',
    'theorem SolC.mono {K T a b : ℝ} {g p q : ℝ → ℝ} (h : SolC K T a g p q) (hab : a ≤ b) :\n    SolC K T b g p q :=')
rep('SolC T ', 'SolC (K : ℝ) T ')
i = s.index('theorem os_neg'); j = s.index('theorem quad_of_psd')
o = s[i:j].replace('theorem os_neg {μ', 'theorem os_neg {K μ').replace('10 * ', 'K * ')
s = s[:i] + o + s[j:]
rep('coefficient-10 field', 'coefficient-K field')
rep('kc1, kc2, kc3, kc4, kB, kx1, kx2, kx3, kx4, kx5, kx6⟩', 'kc1, kc2, kc3, kc4, kB, kx1, kx2, kx3, kx4, kx5, kx6, kK⟩')
rep('      + ((qabs (defect3 c) c.h : ℚ) : ℝ) ^ 2 < (c.ε : ℝ) ^ 2 := by exact_mod_cast kdef',
    '      + ((qabs (defect3 K c) c.h : ℚ) : ℝ) ^ 2 < (c.ε : ℝ) ^ 2 := by exact_mod_cast kdef\n  have hK : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast kK')
rep('(F3 := fun t y1 y2 y3 => -(10 * cl', '(F3 := fun t y1 y2 y3 => -((K : ℝ) * cl')
rep('have d3 := abs_le_qabs (defect3 c) hσ.1 hσ.2', 'have d3 := abs_le_qabs (defect3 K c) hσ.1 hσ.2')
rep('rw [← defect3_eval] at d3', 'rw [← defect3_eval K] at d3')
rep('''      have e3 : dEvalQ c.pq (t - c.t0) - (-(10 * evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0)) + 1
            - evalQ c.pp (t - c.t0) ^ 2)
          = dEvalQ c.pq (t - c.t0) + 10 * evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0) - 1''',
'''      have e3 : dEvalQ c.pq (t - c.t0) - (-((K : ℝ) * evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0)) + 1
            - evalQ c.pp (t - c.t0) ^ 2)
          = dEvalQ c.pq (t - c.t0) + (K : ℝ) * evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0) - 1''')
rep('''      have hm : ((10 * mlo c : ℚ) : ℝ) ≤ 10 * y1 := by
        have := hlo _ hσ
        unfold mlo; push_cast at this ⊢
        linarith [(abs_le.1 he1).1]''',
'''      have hm : ((K * mlo c : ℚ) : ℝ) ≤ (K : ℝ) * y1 := by
        have := hlo _ hσ
        have hy : ((mlo c : ℚ) : ℝ) ≤ y1 := by
          unfold mlo; push_cast at this ⊢
          linarith [(abs_le.1 he1).1]
        push_cast; exact mul_le_mul_of_nonneg_left hy hK''')
rep('''      have hql2 : ((10 * qlo c : ℚ) : ℝ) ≤ 10 * evalQ c.pq (t - c.t0) := by
        have := hql _ hσ; push_cast; linarith
      have hqh2 : 10 * evalQ c.pq (t - c.t0) ≤ ((10 * qhi c : ℚ) : ℝ) := by
        have := hqh _ hσ; push_cast; linarith''',
'''      have hql2 : ((K * qlo c : ℚ) : ℝ) ≤ (K : ℝ) * evalQ c.pq (t - c.t0) := by
        have := hql _ hσ; push_cast; exact mul_le_mul_of_nonneg_left this hK
      have hqh2 : (K : ℝ) * evalQ c.pq (t - c.t0) ≤ ((K * qhi c : ℚ) : ℝ) := by
        have := hqh _ hσ; push_cast; exact mul_le_mul_of_nonneg_left this hK''')
rep('''      have := os_neg (μ := c.μ) (w1 := c.w1) (w2 := c.w2) (m := ((10 * mlo c : ℚ) : ℝ))
        (ql := ((10 * qlo c : ℚ) : ℝ)) (qh := ((10 * qhi c : ℚ) : ℝ))''',
'''      have := os_neg (K := (K : ℝ)) (μ := c.μ) (w1 := c.w1) (w2 := c.w2) (m := ((K * mlo c : ℚ) : ℝ))
        (ql := ((K * qlo c : ℚ) : ℝ)) (qh := ((K * qhi c : ℚ) : ℝ))''')
rep('0 ≤ p, q < 3(1 − p), g > 11/30, with', '0 ≤ p, q < 3(1 − p), g > 11/15, with')
rep('qeval c.pq c.h + c.B < 3 * (1 - (qeval c.pp c.h + c.r2)) ∧ 11 / 30 < qeval c.pg c.h - c.r1)',
    'qeval c.pq c.h + c.B < 3 * (1 - (qeval c.pp c.h + c.r2)) ∧ 11 / 15 < qeval c.pg c.h - c.r1)')
rep('(0 ≤ p T ∧ q T < 3 * (1 - p T) ∧ 11 / 30 < g T)', '(0 ≤ p T ∧ q T < 3 * (1 - p T) ∧ 11 / 15 < g T)')
rep("have kg' : ((11 / 30 : ℚ) : ℝ)", "have kg' : ((11 / 15 : ℚ) : ℝ)")
assert '10 *' not in s, [l for l in s.splitlines() if '10 *' in l]
assert '11 / 30' not in s
open('Work/FSSep/SCellWC.lean', 'w').write(s)
print('ok')
