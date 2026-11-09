import Mathlib
import Work.FalknerSkan.NegTenth

/-!
# Falkner–Skan β = −1/10: the blind restatement, closed (run 2026-11-09T0828Z)

The two theorems are the blind restater's text (Sonnet, from the claims in words only;
`runs/2026-11-09T0828Z/blind2/NegTenthBlind.lean`), copied verbatim with their placeholder proofs
replaced by proofs from `Work.FalknerSkan.NegTenth`.
-/

namespace Blind.NegTenth

open Filter Set Topology

/-- `(f, f1, f2, f3)` represents a solution of the Falkner–Skan equation
`f''' + f f'' + β (1 - (f')²) = 0` with `β = -1/10` on `[0, ∞)`: `f1, f2, f3` are `f', f'', f'''`
(derivatives within `Ici 0`, one-sided at 0), the ODE holds for all `η ≥ 0`,
`f 0 = 0`, `f' 0 = 0`, and `f' → 1` at infinity. -/
def IsSolution (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ η : ℝ, 0 ≤ η → HasDerivWithinAt f (f1 η) (Ici 0) η) ∧
  (∀ η : ℝ, 0 ≤ η → HasDerivWithinAt f1 (f2 η) (Ici 0) η) ∧
  (∀ η : ℝ, 0 ≤ η → HasDerivWithinAt f2 (f3 η) (Ici 0) η) ∧
  (∀ η : ℝ, 0 ≤ η → f3 η + f η * f2 η + (-1/10 : ℝ) * (1 - (f1 η) ^ 2) = 0) ∧
  f 0 = 0 ∧ f1 0 = 0 ∧
  Tendsto f1 atTop (𝓝 1)

/-- Existence in the fast-approach class: for `β = -1/10` there is a solution with `f'' > 0` on
`[0, ∞)` such that for every real `M`, `f''(η) ≥ M (1 - f'(η))` for all sufficiently large `η`. -/
theorem exists_fast :
    ∃ f f1 f2 f3 : ℝ → ℝ, IsSolution f f1 f2 f3 ∧
      (∀ η : ℝ, 0 ≤ η → 0 < f2 η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - f1 η) ≤ f2 η) := by
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, hpos, hdec⟩ :=
    Work.FalknerSkan.NegTenth.fs_neg_tenth_exists_decay
  refine ⟨f, p, q, fun η => -(f η * q η) - (-1 / 10) * (1 - p η ^ 2),
    ⟨fun η hη => hf η hη, fun η hη => hp η hη, fun η hη => hq η hη, fun η _ => by ring,
      h0, h1, hl⟩, fun η hη => hpos η hη, hdec⟩

/-- Non-uniqueness without the fast-approach condition: for `β = -1/10` there are two solutions,
each with `f'' > 0` and `0 ≤ f' ≤ 1` on `[0, ∞)`, each with `f''(η) < 3 (1 - f'(η))` for all
sufficiently large `η`, and with different wall shears `f''(0)`. -/
theorem not_unique :
    ∃ f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ,
      IsSolution f f1 f2 f3 ∧ IsSolution g g1 g2 g3 ∧
      (∀ η : ℝ, 0 ≤ η → 0 < f2 η ∧ 0 ≤ f1 η ∧ f1 η ≤ 1) ∧
      (∀ η : ℝ, 0 ≤ η → 0 < g2 η ∧ 0 ≤ g1 η ∧ g1 η ≤ 1) ∧
      (∀ᶠ η in atTop, f2 η < 3 * (1 - f1 η)) ∧
      (∀ᶠ η in atTop, g2 η < 3 * (1 - g1 η)) ∧
      f2 0 ≠ g2 0 := by
  obtain ⟨f, p, q, g, p₂, q₂, hf, hp, hq, hg, hp₂, hq₂, f0, p0, g0, p₂0, hl, hl₂, hb, hb₂,
    hs, hs₂, hne⟩ := Work.FalknerSkan.NegTenth.fs_neg_tenth_not_unique
  refine ⟨f, p, q, fun η => -(f η * q η) - (-1 / 10) * (1 - p η ^ 2),
    g, p₂, q₂, fun η => -(g η * q₂ η) - (-1 / 10) * (1 - p₂ η ^ 2),
    ⟨fun η hη => hf η hη, fun η hη => hp η hη, fun η hη => hq η hη, fun η _ => by ring,
      f0, p0, hl⟩,
    ⟨fun η hη => hg η hη, fun η hη => hp₂ η hη, fun η hη => hq₂ η hη, fun η _ => by ring,
      g0, p₂0, hl₂⟩, fun η hη => hb η hη, fun η hη => hb₂ η hη, hs, hs₂, hne⟩

end Blind.NegTenth
