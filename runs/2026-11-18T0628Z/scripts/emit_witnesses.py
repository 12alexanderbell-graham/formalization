"""Emit the Lean witness section of Checked/Trust/NecessityAR.lean from the bounds of eds_bounds.py
(run 2026-11-18T0628Z). Lean checks every number; this script only writes them."""
import sys
sys.path.insert(0, '.')
from eds_bounds import W, Bb, dist, down, up, kk
from fractions import Fraction as F
def lit(x):
    x = F(x)
    if x.denominator == 1: return f'({x.numerator}:ℝ)' if x >= 0 else f'(({x.numerator}):ℝ)'
    s = f'({x.numerator} / {x.denominator} : ℝ)' if x >= 0 else f'(-{-x.numerator} / {x.denominator} : ℝ)'
    return s
def dec(x):
    return f'{float(x):.6f}'.rstrip('0')
ks = {1: '1 / 2', 3: '3 / 2', 5: '5 / 2'}
out = []
for name, (a2, a3, H, keep) in W.items():
    for i in (1, 3, 5):
        Bl, Bu = Bb(a2, a3, i); Bl, Bu = down(Bl), up(Bu)
        out.append(f'''theorem B_{name}_{i} : ({dec(Bl)} : ℝ) ≤ Bc {lit(a2)} {lit(a3)} ({ks[i]} * (Real.log 2 / Real.log 10)) ∧
    Bc {lit(a2)} {lit(a3)} ({ks[i]} * (Real.log 2 / Real.log 10)) ≤ ({dec(Bu)} : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)
''')
print('\n'.join(out))
