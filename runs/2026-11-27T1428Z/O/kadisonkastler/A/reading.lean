import Mathlib

/-!
Blind reading A of O55, "Strong Kadison–Kastler stability", Theorem 1.1.
-/

namespace ReaderA

universe u

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `M₁`, the closed operator-norm unit ball of a von Neumann algebra `M ⊆ B(H)`. -/
def unitBall (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

/-- The Kadison–Kastler distance, eq. (kk-definition):
`d(M,N) = max { sup_{x∈M₁} inf_{y∈N₁} ‖x−y‖ , sup_{y∈N₁} inf_{x∈M₁} ‖x−y‖ }`.
All index sets are nonempty (`0 ∈ M₁, N₁`) and all values lie in `[0, 1]`
(`inf_y ‖x − y‖ ≤ ‖x − 0‖ ≤ 1`), so the real `⨆`/`⨅` are genuine sups/infs. -/
noncomputable def kkDist (M N : VonNeumannAlgebra H) : ℝ :=
  max (⨆ x : unitBall M, ⨅ y : unitBall N, ‖(x : H →L[ℂ] H) - y‖)
      (⨆ y : unitBall N, ⨅ x : unitBall M, ‖(x : H →L[ℂ] H) - y‖)

/-- Sanity check that the index sets are nonempty: `0 ∈ M₁`. -/
theorem zero_mem_unitBall (M : VonNeumannAlgebra H) : (0 : H →L[ℂ] H) ∈ unitBall M :=
  ⟨zero_mem M, by simp⟩

end

/-- Theorem 1.1 (Strong Kadison–Kastler stability). For every `ε > 0` there is `δ > 0` such
that for every complex Hilbert space `H` and all von Neumann algebras `M, N ⊆ B(H)`
(unital with identity `I_H`) with `d(M,N) < δ`, there is a unitary `u ∈ B(H)` with
`u M u* = N` and `‖u − I_H‖ < ε`. -/
theorem reading_strong_kadison_kastler :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M N : VonNeumannAlgebra H), kkDist M N < δ →
        ∃ u ∈ unitary (H →L[ℂ] H),
          (fun x => u * x * star u) '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H)) ∧
          ‖u - 1‖ < ε := sorry

end ReaderA

/-!
Ambiguities and choices.

1. "Von Neumann algebra M ⊆ B(H), unital with identity I_H": Mathlib's concrete
   `VonNeumannAlgebra H` (a ⋆-subalgebra of `H →L[ℂ] H` equal to its double commutant). It
   extends `StarSubalgebra`, so it automatically contains `1 = I_H`; this matches "unital with
   identity I_H" (no non-unital/degenerate algebras allowed).
2. "Complex Hilbert space": `NormedAddCommGroup H`, `InnerProductSpace ℂ H`, `CompleteSpace H`.
   The text stresses uniformity over all Hilbert spaces of all cardinalities: `δ` is chosen
   before `H` (quantifier order ∀ε ∃δ ∀H ∀M N), and the statement is universe-polymorphic in
   `u` (for each universe, `δ` works for every Hilbert space in that universe). The zero
   Hilbert space is included; the claim is trivial there.
3. Kadison–Kastler distance: written literally with `⨆`/`⨅` over the subtypes `M₁`, `N₁` in
   ℝ. Junk-value check: Real `⨆`/`⨅` are junk (`0`) only for empty or unbounded families; here
   every family is nonempty (`0 ∈ M₁`, see `zero_mem_unitBall`) and bounded (inner infima lie
   in `[0, ‖x‖] ⊆ [0,1]`, bounded below by 0), so the values are the true sup/inf. The second
   term keeps the text's `‖x − y‖` with `x ∈ M₁` inside, `y ∈ N₁` outside.
4. "u M u* = N" read as equality of sets `{u x u* | x ∈ M} = N`. "Unitary u ∈ B(H)":
   `u ∈ unitary (H →L[ℂ] H)` (`u* u = u u* = 1`), with `star` the Hilbert adjoint.
   `‖u − I_H‖` is the operator norm, `I_H = 1 = id`.
5. "δ = δ(ε)": only existence of `δ` depending on `ε` is asserted (no monotonicity or explicit
   formula). Strict inequalities `d(M,N) < δ`, `‖u − I‖ < ε` as in the text.
6. No ℕ subtraction, division, or extended-valued quantities are used.
-/
