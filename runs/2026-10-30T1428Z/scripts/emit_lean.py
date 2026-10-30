"""Emit the Lean algebra lemma `alg` (closure equations with H-derivatives substituted)."""
import re
c=open('cert_lean.out').read().strip().split('\n')
certs={l.split(' : ')[0]:l.split(' : ')[1] for l in c}
h1='(-H ^ 2 * (1 + q))'; h2='(H ^ 3 * (j + 3 * q + 2))'
h3='(-H ^ 4 * (4 * j + 3 * q ^ 2 + 12 * q - s + 6))'
h4='(H ^ 5 * (10 * j * q + 20 * j + l + 30 * q ^ 2 + 60 * q - 5 * s + 24))'
R0=f'(-6 * ({h1} + 2 * H ^ 2))'; R1=f'(-6 * ({h2} + 4 * H * {h1}))'
R2=f'(-6 * ({h3} + 4 * {h1} ^ 2 + 4 * H * {h2}))'; R3=f'(-6 * ({h4} + 12 * {h1} * {h2} + 4 * H * {h3}))'
E1=f'3 * H ^ 2 = 3 * H ^ 2 * Ω + (x0 - {R0}) / 2 - 3 * H * {R1} * x2'
E2=f'-2 * {h1} = 3 * H ^ 2 * Ω + {R2} * x2 + {R1} * ({R1} * x3 - H * x2)'
E3=(f'-2 * x2 * {R1} * {h1} - 2 * {h2} = -3 * H * (3 * H ^ 2 * Ω) + {R3} * x2 + 3 * {R1} * {R2} * x3'
    f' - {h1} * {R1} * x2 - H * {R2} * x2 - H * {R1} ^ 2 * x3')
def lc(s): return s.replace('linear_combination ','')
out=f'''/-- Algebra of the closure system: (11.14), (11.15), (11.20) with `F′ = 1`, `F⁽⁴⁾ = 0`, the
`H`-derivatives written through `(q₀, j₀, s₀, l₀)`. Certificates from
`runs/2026-10-30T1428Z/scripts/cert_lean.py`. -/
lemma alg (q j s l H Ω x0 x2 x3 : ℝ) (hH : H ≠ 0)
    (e1 : {E1})
    (e2 : {E2})
    (e3 : {E3}) :
    correctR q j s l * x0 = -6 * H ^ 2 * (P0 q j s l * Ω + Q0 q j s l) ∧
    correctR q j s l * (6 * H ^ 2) * x2 = -(P2 q j s * Ω + Q2 q j s) ∧
    (j - q - 2) * correctR q j s l * (6 * H ^ 2) ^ 2 * x3 = -(P3 q j s l * Ω + Q3 q j s l) := by
  have h3 : H ^ 3 ≠ 0 := pow_ne_zero 3 hH
  refine ⟨?_, ?_, ?_⟩
  · apply mul_left_cancel₀ h3
    simp only [correctR, P0, Q0]
    linear_combination {lc(certs['T0'])}
  · apply mul_left_cancel₀ h3
    simp only [correctR, P2, Q2]
    linear_combination {lc(certs['T2'])}
  · apply mul_left_cancel₀ h3
    simp only [correctR, P3, Q3]
    linear_combination {lc(certs['T3'])}
'''
open('alg.lean.txt','w').write(out)
