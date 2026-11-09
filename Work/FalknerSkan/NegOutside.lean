import Mathlib
import Work.FalknerSkan.NegTenth

/-!
# Falkner–Skan β = −1/10: two solutions outside the decay class

Frozen in run 2026-11-09T1028Z (statement first, proof follows). The literal-free form of
`Work.FalknerSkan.NegTenth.fs_neg_tenth_not_unique`: instead of the author's constant in
"eventually f'' < 3 (1 − f')", each of the two solutions fails the decay condition of
`Work.FalknerSkan.NegDecay.fs_neg_decay_equal` itself ("for every M, eventually M (1 − f') ≤ f''"),
the condition read blind in `runs/2026-11-09T1028Z/fsn_reader/` (the reader's edge analysis:
algebraic approach fails it, Gaussian approach satisfies it). With `fs_neg_decay_equal` this says:
for β = −1/10 uniqueness holds inside the decay class and fails outside it.
-/

namespace Work.FalknerSkan.NegOutside

open Set Filter Topology

/-- Falkner–Skan with β = −1/10: there are two solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 and 0 ≤ p ≤ 1 on
[0, ∞), neither of which satisfies "for every M, eventually M (1 − p) ≤ q", with different wall
values q(0) ≠ q₂(0). -/
theorem fs_neg_tenth_not_unique_outside :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1 / 10) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q₂ η ∧ 0 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      ¬ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      ¬ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  sorry

end Work.FalknerSkan.NegOutside
