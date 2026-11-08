import Mathlib

/-!
# Homann: the blind restatement (run 2026-11-08T0428Z)

Copied verbatim (module doc added) from `runs/2026-11-08T0428Z/blind/HomannBlind.lean`, written by a
blind restater (Sonnet) from the question alone: the Homann equation as a chain of
`HasDerivWithinAt` facts plus the equation pointwise, the initial-value claims on `Icc 0 6`.
-/

namespace Blind.Homann

/-- `f, f1, f2, f3` solve the Homann ODE chain on the set `S` (derivatives within `S`). -/
def IsSol (S : Set ℝ) (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ x ∈ S, HasDerivWithinAt f (f1 x) S x) ∧
  (∀ x ∈ S, HasDerivWithinAt f1 (f2 x) S x) ∧
  (∀ x ∈ S, HasDerivWithinAt f2 (f3 x) S x) ∧
  (∀ x ∈ S, f3 x + 2 * f x * f2 x + 1 - (f1 x) ^ 2 = 0)

theorem blind_under (f f1 f2 f3 : ℝ → ℝ)
    (hs : IsSol (Set.Icc 0 6) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.3119376938) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 6 ∧ f2 η < 0 ∧ ∀ s ∈ Set.Icc 0 η, f1 s < 1 := by
  sorry

theorem blind_over (f f1 f2 f3 : ℝ → ℝ)
    (hs : IsSol (Set.Icc 0 6) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.3119376939) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 6 ∧ 1 < f1 η ∧ ∀ s ∈ Set.Icc 0 η, 0 < f2 s := by
  sorry

theorem blind_exists :
    ∃ f f1 f2 f3 : ℝ → ℝ, IsSol (Set.Ici 0) f f1 f2 f3 ∧
      f 0 = 0 ∧ f1 0 = 0 ∧
      Filter.Tendsto f1 Filter.atTop (nhds 1) ∧
      1.3119376938 < f2 0 ∧ f2 0 < 1.3119376939 := by
  sorry

end Blind.Homann
