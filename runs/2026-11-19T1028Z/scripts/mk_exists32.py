"""Writes Work/Math/LE32ExistsLeft.lean from Checked/Math/LEExistsLeft.lean (index three): the
clamped cube g y = cl (6/5) y ^ 3 replaced by the clamped power g y = √(cl (6/5) y) ^ 3, whose
bound (6/5)^(3/2) ≤ 1.728 and Lipschitz constant 3/2 · 11/10 ≤ 9/2 are within the index-three
constants, so the contraction argument is unchanged."""
s = open('Checked/Math/LEExistsLeft.lean').read()
a = s.index("/-- Clamped cube. -/")
b = s.index("theorem h12")
newg = '''/-- Clamped power three halves. -/
noncomputable def g (y : ℝ) : ℝ := Work.Math.LE32Cell.g32 (cl (6 / 5) y)

theorem continuous_g : Continuous g :=
  (Real.continuous_sqrt.comp (continuous_cl _)).pow 3

theorem abs_g_le (y : ℝ) : |g y| ≤ 1.728 := by
  have h := abs_cl_le (by norm_num : (0 : ℝ) ≤ 6 / 5) y
  have hs := Work.Math.LE32Cell.sqrt_le_of (S := 11 / 10) h (by norm_num) (by norm_num)
  unfold g Work.Math.LE32Cell.g32
  rw [abs_of_nonneg (by positivity)]
  calc Real.sqrt (cl (6 / 5) y) ^ 3 ≤ (11 / 10) ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 3
    _ ≤ 1.728 := by norm_num

theorem g_sub (y z : ℝ) : |g y - g z| ≤ 9 / 2 * |y - z| := by
  unfold g
  have := Work.Math.LE32Cell.g32_lip (TH := 6 / 5) (S := 11 / 10)
    (abs_cl_le (by norm_num) y) (abs_cl_le (by norm_num) z) (by norm_num) (by norm_num)
  have hc := cl_sub (6 / 5) y z
  nlinarith [abs_nonneg (cl (6 / 5) y - cl (6 / 5) z)]

theorem g_of_abs_le {y : ℝ} (h : |y| ≤ 6 / 5) : g y = Work.Math.LE32Cell.g32 y := by
  unfold g; rw [cl_of_abs_le h]

'''
s = s[:a] + newg + s[b:]
R = [("namespace Checked.Math.LEExistsLeft", "namespace Work.Math.LE32ExistsLeft"),
     ("end Checked.Math.LEExistsLeft", "end Work.Math.LE32ExistsLeft"),
     ("import Checked.Math.LEExistsRight", "import Checked.Math.LEExistsRight\nimport Work.Math.LE32Cell"),
     ("θL x ^ 3", "Work.Math.LE32Cell.g32 (θL x)"), ("θ x ^ 3", "Work.Math.LE32Cell.g32 (θ x)")]
for x, y in R:
    assert x in s, x
    s = s.replace(x, y)
i = s.index("/-!"); j = s.index("-/", i) + 2
s = s[:i] + '''/-!
# Lane–Emden index three halves: a solution regular at the singular point, near the centre

The index-three construction `Checked.Math.LEExistsLeft` (Banach fixed point of the scaled Volterra
map on [0, 1/2]) with the clamped power three halves g y = √(cl (6/5) y) ^ 3 in place of the
clamped cube; written by `runs/2026-11-19T1028Z/scripts/mk_exists32.py`.
-/''' + s[j:]
open('Work/Math/LE32ExistsLeft.lean', 'w').write(s)
