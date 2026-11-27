import Mathlib

namespace ReaderB

/-- Torsion-free group: no nontrivial element of finite order. -/
def TorsionFreeGroup (G : Type) [Group G] : Prop := ∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g

/-- Finitely presented: isomorphic to `⟨x₁..xₙ | R⟩` with `R` a finite set of relators. -/
def FinitelyPresentedGroup (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (R : Set (FreeGroup (Fin n))), R.Finite ∧ Nonempty (PresentedGroup R ≃* G)

/-- `G` admits a finite two-dimensional classifying space: a path-connected topological space `X`,
which is a finite CW complex with no cells in dimension ≥ 3, with a contractible covering space
(so `X` is aspherical) and `π₁(X) ≅ G`. -/
def HasFiniteTwoDimClassifyingSpace (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X) (_ : PathConnectedSpace X)
    (_ : Topology.CWComplex (Set.univ : Set X)),
    (∀ n : ℕ, 3 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
    (∀ n : ℕ, Finite (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
    (∃ (E : Type) (_ : TopologicalSpace E) (p : E → X),
        Continuous p ∧ IsCoveringMap p ∧ ContractibleSpace E) ∧
    ∃ x : X, Nonempty (CategoryTheory.Aut (FundamentalGroupoid.mk x) ≃* G)

/-- Theorem 1.1, first part. -/
theorem reading_zerodiv_main :
    ∃ (G : Type) (_ : Group G), FinitelyPresentedGroup G ∧ TorsionFreeGroup G ∧
      ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0 := sorry

/-- The "Moreover" clause, as a separate theorem. -/
theorem reading_zerodiv_moreover :
    ∃ (G : Type) (_ : Group G), FinitelyPresentedGroup G ∧ TorsionFreeGroup G ∧
      HasFiniteTwoDimClassifyingSpace G := sorry

/-- Theorem 1.1 in full (conjoined: same `G`). -/
theorem reading_zerodiv_full :
    ∃ (G : Type) (_ : Group G), FinitelyPresentedGroup G ∧ TorsionFreeGroup G ∧
      (∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0) ∧
      HasFiniteTwoDimClassifyingSpace G := sorry

/-- Kaplansky's zero-divisor conjecture is false:  it asserts `K[G]` has no nonzero zero divisors for
every field `K` and torsion-free group `G`. -/
theorem reading_zerodiv_kaplansky_false :
    ¬ (∀ (K : Type) [Field K] (G : Type) [Group G], TorsionFreeGroup G →
        ∀ α β : MonoidAlgebra K G, α * β = 0 → α = 0 ∨ β = 0) := sorry

end ReaderB

/-
Ambiguities and choices.
* 𝔽₂ is `ZMod 2`; 𝔽₂[G] is `MonoidAlgebra (ZMod 2) G` (finitely supported functions, bilinear
  multiplication extended from the group law).  Nonzero zero divisor pair: α ≠ 0, β ≠ 0, α*β = 0.
* Groups live in `Type` (universe 0); any group in the theorem is countable so nothing is lost.
* Torsion-free = no nontrivial element of finite order (I did NOT use Mathlib's `IsMulTorsionFree`,
  which is a unique-roots condition for commuting elements and is a different notion).
* Finitely presented: `PresentedGroup R ≃* G` with finitely many generators `Fin n` and finite `R`.
* "Finite two-dimensional classifying space": the paper does not define it in the excerpt.  I read it as a
  K(G,1) that is a finite CW complex of dimension ≤ 2 (Mathlib's classical `CWComplex` on `Set.univ`,
  finitely many cells in each dimension and none from dimension 3 up, hence finitely many in total),
  path-connected, with π₁ ≅ G, and aspherical expressed as having a contractible covering space.
  Exactly "dimension 2" (rather than ≤ 2) is not demanded; with G nontrivial torsion-free this is
  equivalent in spirit but I did not add the extra condition.  Fundamental group is the automorphism
  group of the point in the fundamental groupoid (`FundamentalGroup X x` abbrev unfolds to `End`; I used
  `Aut` so that it is a group; the iso with G is a `MulEquiv`).
* The conjectural statement: for all fields K and torsion-free G, no nonzero zero divisors (I did not
  restrict to finitely presented G, matching the first sentence).  Negated as a whole.
* No junk values: no division, subtraction, cardinalities.
-/
