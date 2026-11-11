import Mathlib

/-!
# Falkner–Skan separation: at most one pressure-gradient parameter has a separation profile

Frozen in run 2026-11-11T0232Z (statement first, proof follows). Same β-form system and class as
`Work.FalknerSkan.Separation.fs_separation_exists` (f' = p, p' = q, q' = −f q − β (1 − p²),
one-sided derivatives at 0, f(0) = p(0) = q(0) = 0, p → 1, q > 0 on (0, ∞), and for every M
eventually M (1 − p) ≤ q). Together with that theorem: the separation value β* is unique and lies
in (−0.1988377351, −0.1988377350).
Proof plan: referee `runs/2026-11-11T0232Z/referee/REPORT.md` §1.3 (Crocco variables in the
β-form; z ~ √(2|β| t) at the wall orders the two profiles; no-crossing and the tail estimate of
Theorem U′, `Work/FalknerSkan/NegUPrime.lean`).
-/

namespace Work.FalknerSkan.SeparationUnique

open Set Filter Topology

/-- Falkner–Skan separation is unique in β: if (f₁, p₁, q₁) solves f''' + f f'' + β₁(1 − f'²) = 0
and (f₂, p₂, q₂) solves the same equation with β₂, both on [0, ∞) with f(0) = 0, p(0) = 0, zero wall
shear q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M, eventually M (1 − p) ≤ q, then β₁ = β₂. -/
theorem fs_separation_unique {β₁ β₂ : ℝ} {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ}
    (hf₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₁ (p₁ η) (Ici 0) η)
    (hp₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₁ (q₁ η) (Ici 0) η)
    (hq₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₁ (-(f₁ η * q₁ η) - β₁ * (1 - p₁ η ^ 2)) (Ici 0) η)
    (hf₁0 : f₁ 0 = 0) (hp₁0 : p₁ 0 = 0) (hq₁0 : q₁ 0 = 0) (hl₁ : Tendsto p₁ atTop (𝓝 1))
    (hpos₁ : ∀ η ∈ Ioi (0 : ℝ), 0 < q₁ η) (hdec₁ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₁ η) ≤ q₁ η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β₂ * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hq₂0 : q₂ 0 = 0) (hl₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ioi (0 : ℝ), 0 < q₂ η) (hdec₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    β₁ = β₂ := by
  sorry

end Work.FalknerSkan.SeparationUnique
