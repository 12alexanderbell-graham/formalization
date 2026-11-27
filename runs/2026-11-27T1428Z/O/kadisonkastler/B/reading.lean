import Mathlib

namespace ReaderB

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closed operator-norm unit ball of a von Neumann algebra, as a subtype. -/
def unitBall (M : VonNeumannAlgebra H) : Type u := {x : H →L[ℂ] H // x ∈ M ∧ ‖x‖ ≤ 1}

instance (M : VonNeumannAlgebra H) : Nonempty (unitBall M) :=
  ⟨⟨0, zero_mem M, by simp⟩⟩

/-- Kadison–Kastler distance, literally the formula of the text:
max { sup_{x∈M₁} inf_{y∈N₁} ‖x−y‖ , sup_{y∈N₁} inf_{x∈M₁} ‖x−y‖ }.
All index types are nonempty (0 lies in both balls) and all values lie in [0,2], so the real
`⨆`/`⨅` are the genuine sup/inf, not junk values. -/
noncomputable def kkDist (M N : VonNeumannAlgebra H) : ℝ :=
  max (⨆ x : unitBall M, ⨅ y : unitBall N, ‖x.1 - y.1‖)
      (⨆ y : unitBall N, ⨅ x : unitBall M, ‖x.1 - y.1‖)

/-- Theorem 1.1 (for Hilbert spaces in universe `u`): δ depends only on ε. -/
theorem readingKadisonKastler (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M N : VonNeumannAlgebra H), kkDist M N < δ →
        ∃ u : unitary (H →L[ℂ] H),
          (fun x : H →L[ℂ] H => (u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) '' (M : Set (H →L[ℂ] H))
            = (N : Set (H →L[ℂ] H)) ∧
          ‖(u : H →L[ℂ] H) - 1‖ < ε := sorry

end ReaderB

/-
Ambiguities and choices.
* "Unital von Neumann algebra with identity I_H": Mathlib's `VonNeumannAlgebra H` is a
  star-subalgebra of `H →L[ℂ] H` equal to its double commutant, so it contains 1 = I_H
  (unital is built in).
* "Every complex Hilbert space": a complete complex inner product space `H`. Lean cannot quantify
  over all universes in one statement, so H ranges over `Type u` for an arbitrary fixed universe u
  (the theorem is universe-polymorphic), with δ chosen before H. A δ uniform across universes
  would follow from universe-independence of the claim but is not literally expressible.
* Distance: sup/inf over closed unit balls written with `⨆`/`⨅` over subtypes in ℝ. These are
  nonempty (0 ∈ ball) and bounded (norms of differences ≤ 2, ≥ 0), so no junk value; no ⊤/ENNReal.
  `d(M,N) < δ` is the strict inequality of the text (not the weaker "each x has a close y").
* Conjugation: u M u* = N as equality of sets of operators, image of M under x ↦ u x u*, with
  u in `unitary (H →L[ℂ] H)` (u*u = uu* = 1). ‖u − I_H‖ < ε is operator norm.
* Both M and N must act on the same H, as in the text. Real ε, δ; no subtraction in ℕ.
-/
