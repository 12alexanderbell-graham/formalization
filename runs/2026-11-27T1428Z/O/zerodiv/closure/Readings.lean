import Mathlib

/-! # Target O, family zerodiv: the three blind readings of run 2026-11-27T1428Z (brief 0ed6b5c), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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
