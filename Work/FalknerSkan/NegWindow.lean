import Mathlib

/-!
# Falkner–Skan β = −1/10 (adverse pressure gradient): ten-decimal window of the wall shear of the
# decay-class solution

Program β-form with β = −1/10: f' = p, p' = q, q' = −f q − β (1 − p²), one-sided derivatives at 0,
f(0) = 0, p(0) = 0, p → 1. The class of `Work.FalknerSkan.NegDecay.fs_neg_decay_equal`: q > 0 on
[0, ∞) and, for every M, eventually M (1 − p) ≤ q. Route: certified chains at the scaled window
ends (Slow at 1.009619629, Over at 1.0096196292; `runs/2026-11-09T1228Z/scripts/make_window.sh`),
the supremum argument (`Work.FSNeg.NWindow.core_window`), scaling by √10, and the uniqueness and
largest-shear theorems of `Work.FalknerSkan.NegDecay`.

Frozen in run 2026-11-09T1228Z (statements first, proofs follow): statements only (`sorry`), not yet imported by `Work.lean`; scratch proofs compiled in `runs/2026-11-09T1228Z/lean/`.
-/

namespace Work.FalknerSkan.NegWindow

open Set Filter Topology

/-- Falkner–Skan with β = −1/10: every solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, has 0.3192697598 < q(0) < 0.3192697599. -/
theorem fs_neg_tenth_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.3192697598 < q 0 ∧ q 0 < 0.3192697599 := by
  sorry

/-- Falkner–Skan with β = −1/10: every solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1 and q > 0 on [0, ∞) (no condition on how p approaches 1)
has q(0) < 0.3192697599. -/
theorem fs_neg_tenth_monotone_lt (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    q 0 < 0.3192697599 := by
  sorry

end Work.FalknerSkan.NegWindow
