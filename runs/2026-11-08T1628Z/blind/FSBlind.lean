import Mathlib

namespace Blind.FSHalf

open Set Filter Topology

/-- `f, f1, f2, f3` : `f1 = f'`, `f2 = f''`, `f3 = f'''` on `[0,∞)` (one-sided derivatives at 0). -/
structure IsSol (f f1 f2 f3 : ℝ → ℝ) : Prop where
  d0 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f (f1 x) (Ici 0) x
  d1 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f1 (f2 x) (Ici 0) x
  d2 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f2 (f3 x) (Ici 0) x
  ode : ∀ x ∈ Ici (0:ℝ), f3 x + f x * f2 x + (1/2) * (1 - (f1 x)^2) = 0
  bc0 : f 0 = 0
  bc1 : f1 0 = 0
  bcinf : Tendsto f1 atTop (𝓝 1)

theorem fs_W (f f1 f2 f3 : ℝ → ℝ) (h : IsSol f f1 f2 f3)
    (hb : ∀ x ∈ Ici (0:ℝ), -1 ≤ f1 x ∧ f1 x ≤ 1) :
    (0.927680039 : ℝ) < f2 0 ∧ f2 0 < 0.927680040 := by
  sorry

theorem fs_U (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (h : IsSol f f1 f2 f3) (h' : IsSol g g1 g2 g3)
    (hb : ∀ x ∈ Ici (0:ℝ), -1 ≤ f1 x ∧ f1 x ≤ 1)
    (hb' : ∀ x ∈ Ici (0:ℝ), -1 ≤ g1 x ∧ g1 x ≤ 1) :
    ∀ x ∈ Ici (0:ℝ), f x = g x ∧ f1 x = g1 x ∧ f2 x = g2 x := by
  sorry

theorem fs_E : ∃ f f1 f2 f3 : ℝ → ℝ, IsSol f f1 f2 f3 ∧
    (∀ x ∈ Ici (0:ℝ), 0 ≤ f1 x ∧ f1 x < 1) ∧
    (0.927680039 : ℝ) < f2 0 ∧ f2 0 < 0.927680040 := by
  sorry

end Blind.FSHalf
