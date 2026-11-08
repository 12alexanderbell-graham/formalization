import Mathlib
import Work.Homann.HomannBlind
import Work.Homann.Homann

/-!
# Homann shooting events: the blind restatement, closed

The blind restater's `Blind.Homann.blind_under` and `blind_over` (run 2026-11-08T0428Z: a quadruple
f, f1, f2, f3 with derivatives within [0, 6] and the equation f3 + 2 f f2 + 1 − f1² = 0 pointwise)
follow from the program's frozen `Work.Homann.homann_under` and `homann_over` with S = 6.
The blind `blind_exists` (a quadruple on [0, ∞) with the equation pointwise) follows from
`Work.Homann.homann_exists` with f3 := −2 f f2 − 1 + f1².
-/

namespace Work.Homann.BlindClosed
open Set Filter Topology

theorem under_closed (f f1 f2 f3 : ℝ → ℝ)
    (h : Blind.Homann.IsSol (Set.Icc 0 6) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.3119376938) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 6 ∧ f2 η < 0 ∧ ∀ s ∈ Set.Icc 0 η, f1 s < 1 := by
  obtain ⟨hf, hp, hq, he⟩ := h
  obtain ⟨η, hη, k1, k2⟩ := Work.Homann.homann_under 6 le_rfl f f1 f2 hf hp
    (fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht)) h0 h1 h2
  exact ⟨η, hη.1, hη.2, k1, k2⟩

theorem over_closed (f f1 f2 f3 : ℝ → ℝ)
    (h : Blind.Homann.IsSol (Set.Icc 0 6) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.3119376939) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 6 ∧ 1 < f1 η ∧ ∀ s ∈ Set.Icc 0 η, 0 < f2 s := by
  obtain ⟨hf, hp, hq, he⟩ := h
  obtain ⟨η, hη, k1, k2⟩ := Work.Homann.homann_over 6 le_rfl f f1 f2 hf hp
    (fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht)) h0 h1 h2
  exact ⟨η, hη.1, hη.2, k1, k2⟩

theorem exists_closed :
    ∃ f f1 f2 f3 : ℝ → ℝ, Blind.Homann.IsSol (Set.Ici 0) f f1 f2 f3 ∧
      f 0 = 0 ∧ f1 0 = 0 ∧ Filter.Tendsto f1 Filter.atTop (nhds 1) ∧
      1.3119376938 < f2 0 ∧ f2 0 < 1.3119376939 := by
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩ := Work.Homann.homann_exists
  exact ⟨f, p, q, fun t => -(2 * f t * q t) - 1 + p t ^ 2, ⟨hf, hp, hq, fun t _ => by ring⟩,
    h0, h1, hl, hlo, hhi⟩

end Work.Homann.BlindClosed
