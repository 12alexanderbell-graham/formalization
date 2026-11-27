import Mathlib

namespace ReaderC

/-- My model of "G admits a finite two-dimensional classifying space" (a K(G,1)):
there is a finite abstract-style geometric simplicial complex `K` in some Euclidean
space `ℝ^N` with all faces finite of at most 3 vertices (dimension at most 2), whose
realization `K.space` (a subspace of `ℝ^N`) has a basepoint `x` with fundamental group
isomorphic to `G`, and which has a covering `p : Y → K.space` from a contractible space
`Y` (so `p` is the universal cover). -/
def HasFinite2DimClassifyingSpace (G : Type) [Group G] : Prop :=
  ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
    K.faces.Finite ∧ (∀ s ∈ K.faces, s.card ≤ 3) ∧
    ∃ x : K.space,
      Nonempty (FundamentalGroup (↥K.space) x ≃* G) ∧
      ∃ (Y : Type) (_ : TopologicalSpace Y) (p : Y → K.space),
        IsCoveringMap p ∧ ContractibleSpace Y

/-- Theorem 1.1, first part: finitely presented torsion-free `G` and nonzero `α, β ∈ 𝔽₂[G]`
with `αβ = 0`. -/
theorem reading_zerodiv_thm1_1_part1 :
    ∃ (G : Type) (_ : Group G), IsMulTorsionFree G ∧ Group.IsFinitelyPresented G ∧
      ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0 := by
  sorry

/-- Theorem 1.1, "Moreover" clause, as a separate statement: there is a finitely presented
torsion-free group admitting a finite two-dimensional classifying space. -/
theorem reading_zerodiv_thm1_1_moreover :
    ∃ (G : Type) (_ : Group G), IsMulTorsionFree G ∧ Group.IsFinitelyPresented G ∧
      HasFinite2DimClassifyingSpace G := by
  sorry

/-- Theorem 1.1 in full: the same `G` carries nonzero `α, β` with `αβ = 0` AND admits a
finite two-dimensional classifying space. -/
theorem reading_zerodiv_thm1_1_conjoined :
    ∃ (G : Type) (_ : Group G), IsMulTorsionFree G ∧ Group.IsFinitelyPresented G ∧
      (∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0) ∧
      HasFinite2DimClassifyingSpace G := by
  sorry

/-- "Kaplansky's zero-divisor conjecture is false": the conjecture is that for every field `K`
and torsion-free group `G`, `K[G]` has no nonzero zero divisors, i.e. nonzero `α, β` have
`αβ ≠ 0`. Its negation is stated here. -/
theorem reading_kaplansky_is_false :
    ¬ (∀ (K : Type) [Field K] (G : Type) [Group G],
        IsMulTorsionFree G →
        ∀ α β : MonoidAlgebra K G, α ≠ 0 → β ≠ 0 → α * β ≠ 0) := by
  sorry

/-!
## Ambiguities and choices (reader C, O45)

1. "Torsion-free": Mathlib's `IsMulTorsionFree G` (no nontrivial element of finite
   order; the class is in `Mathlib/Algebra/Group/Torsion.lean`), used for the group. The brief's "Mathlib's group notions may be used" applies.

2. "Finitely presented": Mathlib's `Group.IsFinitelyPresented G`.

3. `𝔽₂[G]` is `MonoidAlgebra (ZMod 2) G`, the group algebra with the field `ZMod 2`. The
   group-algebra product is Mathlib's convolution product (extended bilinearly from the
   group law), so `α * β` is the algebra product.

4. "Finite two-dimensional classifying space" is not in Mathlib, so I wrote my own model
   (`HasFinite2DimClassifyingSpace`). Choices:
   - Model: a finite geometric simplicial complex `K` in `ℝ^N` (Mathlib's
     `SimplicialComplex`), finite face set, each face of card at most 3 (dimension at
     most 2). "Two-dimensional" is read as "dimension at most 2" (lower dimension is
     allowed; a 1- or 0-dimensional space cannot be K(G,1) for nontrivial G anyway).
   - Its realization is `K.space` with the subspace topology; `FundamentalGroup` at a
     point `x` is isomorphic to `G`.
   - Universal cover: there is a covering map `p : Y → K.space` with `Y` contractible
     (contractible implies simply connected, so `p` is a universal cover). This
     formalizes "classifying space" as K(G,1).
   - Caveat: the source says "finite two-dimensional classifying space" without naming
     CW versus simplicial. Every finite 2-dimensional CW complex model is, up to homotopy,
     also a finite simplicial one, but my definition is the simplicial-model reading,
     not a literal CW one.
   - Basepoint: `Nonempty (FundamentalGroup x ≃* G)` is stated for the chosen basepoint
     `x`; `K.space` is nonempty whenever `K` has a face, so the existential over `x`
     is safe.

5. Theorem 1.1 has three readings written: part1 (the zero-divisor witnesses only),
   the "Moreover" clause as a separate theorem (G f.p., torsion-free, with the
   classifying space; it does NOT repeat the zero-divisor witnesses), and the conjoined
   form (the same G with both properties). The source's "Moreover, G admits ..." refers to
   the G of the main statement, so the conjoined theorem is the literal one.

6. "Kaplansky's zero-divisor conjecture is false": the conjecture is read as
   `∀ K field, ∀ G torsion-free, ∀ α β ∈ K[G], α ≠ 0 → β ≠ 0 → α β ≠ 0`; the claim is its
   negation. `K : Type` with `[Field K]`, `G : Type` with `[Group G]`.

7. No junk values are used: no ℕ subtraction, no division, no `ncard`. Cardinality of the
   simplicial faces is `Finset.card` on finite face sets (the face finiteness is stated).
-/

end ReaderC
