import Mathlib

namespace ReaderA

open Topology

/-- A group is torsion-free: no nontrivial element has finite order. -/
def TorsionFree (G : Type) [Group G] : Prop :=
  ∀ g : G, ∀ n : ℕ, 0 < n → g ^ n = 1 → g = 1

/-- The group algebra `K[G]`: finite formal sums of elements of `G` with coefficients in `K`,
multiplication extended bilinearly from the group law (Mathlib's `MonoidAlgebra K G`). -/
abbrev GroupAlgebra (K G : Type) [Field K] [Group G] : Type := MonoidAlgebra K G

/-- `G` admits a finite two-dimensional classifying space: there is a topological space `X`
which is a finite CW complex (finitely many cells in total) with no cells of dimension `> 2`,
and which is a `K(G,1)`: path-connected, `π₁(X, x) ≅ G`, and `πₙ(X, x)` trivial for `n ≥ 2`. -/
def AdmitsFiniteTwoDimClassifyingSpace (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (Set.univ : Set X)),
    RelCWComplex.Finite (Set.univ : Set X) ∧
    (∀ n : ℕ, 2 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
    PathConnectedSpace X ∧
    ∃ x : X, Nonempty (FundamentalGroup X x ≃* G) ∧
      ∀ n : ℕ, 2 ≤ n → Subsingleton (π_ n X x)

/-- Theorem 1.1, first sentence. -/
theorem reading_thm_1_1 :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ TorsionFree G ∧
      ∃ α β : GroupAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0 := sorry

/-- Theorem 1.1, "Moreover" clause on its own.  The clause speaks of "the group" of the theorem,
i.e. a group `G` for which `𝔽₂[G]` has a nonzero zero-divisor pair; stand-alone it is read as:
some group `G` with nonzero `α, β ∈ 𝔽₂[G]`, `αβ = 0`, admits a finite two-dimensional
classifying space.  (See comment block, item 6.) -/
theorem reading_thm_1_1_moreover :
    ∃ (G : Type) (_ : Group G),
      (∃ α β : GroupAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0) ∧
      AdmitsFiniteTwoDimClassifyingSpace G := sorry

/-- Theorem 1.1 in full: the first sentence conjoined with the "Moreover" clause, for one and the
same group `G`. -/
theorem reading_thm_1_1_full :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ TorsionFree G ∧
      (∃ α β : GroupAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0) ∧
      AdmitsFiniteTwoDimClassifyingSpace G := sorry

/-- Kaplansky's zero-divisor conjecture, as stated in the introduction's first sentence:
`K[G]` has no nonzero zero divisors whenever `K` is a field and `G` is torsion-free. -/
def KaplanskyZeroDivisorConjecture : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [Group G], TorsionFree G →
    ∀ α β : GroupAlgebra K G, α * β = 0 → α = 0 ∨ β = 0

/-- "Kaplansky's zero-divisor conjecture is false." -/
theorem reading_kaplansky_false : ¬ KaplanskyZeroDivisorConjecture := sorry

end ReaderA

/-
Reader A -- ambiguities and choices

1. 𝔽₂ is `ZMod 2` (the field with two elements).  `K[G]` / `𝔽₂[G]` is Mathlib's
   `MonoidAlgebra K G` (finitely supported functions `G → K` with convolution product), which
   is exactly "finite formal sums of elements of G, multiplication extended bilinearly".

2. "torsion-free" is my own `TorsionFree`: every `g` with `g ^ n = 1` for some `n > 0` is `1`.
   (Mathlib's current `IsMulTorsionFree` is a different, power-injectivity notion on commuting
   elements; I did not use it.)  "finitely presented" is Mathlib's `Group.IsFinitelyPresented`.

3. "nonzero zero divisors": a pair `α, β`, both nonzero, with `α * β = 0` (the theorem says
   exactly this).  In the conjecture "no nonzero zero divisors" is read as: `αβ = 0` implies
   `α = 0` or `β = 0`, for all `α, β` -- this covers left and right zero divisors, since `K[G]`
   is noncommutative and both orders are quantified.

4. Universes: `G`, `K`, `X` all live in `Type`.  For the existential theorems this is the
   stronger (more specific) reading; for the conjecture, restricting to `Type` makes its
   negation formally a statement about `Type`-valued fields and groups, which is where the
   counterexample lives anyway (with `K = ZMod 2`).

5. "finite two-dimensional classifying space": a classifying space for a discrete group `G`
   is a `K(G,1)`, i.e. a connected CW complex with `π₁ ≅ G` and vanishing higher homotopy
   groups (equivalently, contractible universal cover; I used the homotopy-group form, which
   Mathlib can express).  "finite" = finitely many cells: Mathlib's `RelCWComplex.Finite`
   (finite type and finite dimensional), applied to `Set.univ` in a Hausdorff space `X` with a
   Mathlib (classical) `CWComplex` structure.  "two-dimensional" read as "dimension at most 2":
   `cell n` empty for `n > 2`.  The stricter reading "dimension exactly 2" (some 2-cell) would
   add `Nonempty (CWComplex.cell univ 2)`; for this group the two readings are equivalent in
   mathematical content (a group with dimension ≤ 1 `K(G,1)` is free, and free group rings
   have no zero divisors), so I kept the weaker, standard one.  Path-connected is required
   ("connected" for a CW complex).  `π_ n X x` trivial is `Subsingleton`; `π₁ ≅ G` is a
   group isomorphism `FundamentalGroup X x ≃* G`.  The base point choice is irrelevant
   because `X` is path-connected.

6. The "Moreover" clause refers to the group `G` of the first sentence.  Taken in complete
   isolation ("some group admits a finite 2-dimensional classifying space") it would be
   trivially true (e.g. `ℤ`, the circle), so for the stand-alone theorem
   `reading_thm_1_1_moreover` I kept the identifying property of "the group" that the clause
   is about -- a nonzero zero-divisor pair in `𝔽₂[G]` -- and dropped "finitely presented" and
   "torsion-free" (both of which in fact follow from having a finite aspherical CW model, but
   I did not add them).  The faithful full statement, with one and the same `G` carrying all
   properties, is `reading_thm_1_1_full`.

7. No junk values: no division, subtraction, ncard, sSup/sInf or ℕ∞ appear.
-/
