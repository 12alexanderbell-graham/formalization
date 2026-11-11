import Mathlib
import Work.FalknerSkan.SeparationUnique

/-!
# Falkner–Skan separation uniqueness: the blind restatement, closed (run 2026-11-11T0232Z)

The definition and theorem below are the blind restater's text (Sonnet, from the claim in words
only; `runs/2026-11-11T0232Z/blind2/SepUniqueBlind.lean`), copied verbatim with the placeholder
proof replaced by a proof from `Work.FalknerSkan.SeparationUnique.fs_separation_unique`: the blind
profile is C³ on [0, ∞) with `derivWithin` derivatives, which give the one-sided derivative facts of
the frozen statement directly.
-/

namespace Blind.SepUnique

open Filter Topology Set

/-- `f` is a separation profile for the Falkner–Skan equation with parameter `β`:
derivatives are taken within `[0,∞)`. -/
def IsSepProfile (β : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici 0) ∧
  (∀ η ∈ Ici (0:ℝ),
    derivWithin (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) η
      + f η * derivWithin (derivWithin f (Ici 0)) (Ici 0) η
      + β * (1 - (derivWithin f (Ici 0) η) ^ 2) = 0) ∧
  f 0 = 0 ∧ derivWithin f (Ici 0) 0 = 0 ∧
  Tendsto (derivWithin f (Ici 0)) atTop (𝓝 1) ∧
  derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 = 0 ∧
  (∀ η > (0:ℝ), 0 < derivWithin (derivWithin f (Ici 0)) (Ici 0) η) ∧
  (∀ M : ℝ, ∀ᶠ η in atTop,
    M * (1 - derivWithin f (Ici 0) η) ≤ derivWithin (derivWithin f (Ici 0)) (Ici 0) η)

/-- The one-sided derivative facts of a blind separation profile. -/
theorem facts {β : ℝ} {f : ℝ → ℝ} (h : IsSepProfile β f) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (derivWithin f (Ici 0) η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (derivWithin f (Ici 0))
      (derivWithin (derivWithin f (Ici 0)) (Ici 0) η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (derivWithin (derivWithin f (Ici 0)) (Ici 0))
      (-(f η * derivWithin (derivWithin f (Ici 0)) (Ici 0) η)
        - β * (1 - derivWithin f (Ici 0) η ^ 2)) (Ici 0) η) := by
  obtain ⟨hC, hode, -⟩ := h
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have C1 : ContDiffOn ℝ 2 (derivWithin f (Ici 0)) (Ici 0) := hC.derivWithin hu (by norm_num)
  have C2 : ContDiffOn ℝ 1 (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) :=
    C1.derivWithin hu (by norm_num)
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · exact ((hC.differentiableOn (by norm_num)) η hη).hasDerivWithinAt
  · exact ((C1.differentiableOn (by norm_num)) η hη).hasDerivWithinAt
  · refine ((C2.differentiableOn (by norm_num)) η hη).hasDerivWithinAt.congr_deriv ?_
    linarith [hode η hη]

theorem blind_sep_unique (β₁ β₂ : ℝ) (f₁ f₂ : ℝ → ℝ)
    (h₁ : IsSepProfile β₁ f₁) (h₂ : IsSepProfile β₂ f₂) : β₁ = β₂ := by
  obtain ⟨a1, a2, a3⟩ := facts h₁
  obtain ⟨b1, b2, b3⟩ := facts h₂
  obtain ⟨-, -, c0, c1, c2, c3, c4, c5⟩ := h₁
  obtain ⟨-, -, d0, d1, d2, d3, d4, d5⟩ := h₂
  exact Work.FalknerSkan.SeparationUnique.fs_separation_unique a1 a2 a3 c0 c1 c3 c2
    (fun η hη => c4 η hη) c5 b1 b2 b3 d0 d1 d3 d2 (fun η hη => d4 η hη) d5

end Blind.SepUnique

#print axioms Blind.SepUnique.blind_sep_unique
