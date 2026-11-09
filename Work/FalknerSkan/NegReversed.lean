import Mathlib

/-!
# Falkner–Skan β = −1/10 (adverse pressure gradient): a reversed-flow solution, and two solutions
# in the decay class

Program β-form with β = −1/10: f' = p, p' = q, q' = −f q − β (1 − p²), one-sided derivatives at 0,
f(0) = 0, p(0) = 0, p → 1. Route: certified chains in scaled variables (K = 10) — Over at
−0.4444461497, the lower Slow event at −0.4444461493 and a tube around the window on [0, 3/2]
(`runs/2026-11-09T1228Z/scripts/make_lower.sh`) — the supremum argument
(`Work.FSNeg.LAssemble.core_lower`) and scaling by √10.

Frozen in run 2026-11-09T1228Z (statements first, proofs follow): statements only (`sorry`), not yet imported by `Work.lean`; scratch proofs compiled in `runs/2026-11-09T1228Z/lean/`.
-/

namespace Work.FalknerSkan.NegReversed

open Set Filter Topology

/-- Falkner–Skan with β = −1/10: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies −0.1405462131 < q(0) < −0.1405462129 (reversed flow
at the wall). -/
theorem fs_neg_tenth_reversed :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1405462131 < q 0 ∧ q 0 < -0.1405462129 := by
  sorry

/-- Falkner–Skan with β = −1/10: there are two solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on
[0, ∞) and, for every M, eventually M (1 − p) ≤ q, whose values q(0) and q₂(0) differ. -/
theorem fs_neg_tenth_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1 / 10) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  sorry

end Work.FalknerSkan.NegReversed
