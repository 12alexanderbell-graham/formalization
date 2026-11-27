import Mathlib

namespace ReaderA

/-- A real normed space is reflexive if the canonical embedding into its bidual
(`x ↦ (f ↦ f x)`, continuous duals throughout) is surjective. -/
def IsReflexive (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

/-- `F : C → C` is nonexpansive in the given norm of `X`. -/
def Nonexpansive {X : Type*} [NormedAddCommGroup X] {C : Set X} (F : C → C) : Prop :=
  ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖

/-- The common fixed set `Fix(𝒮) = {x ∈ C : T x = x for every T ∈ 𝒮}`, as a subset of `C`. -/
def commonFix {X : Type*} {C : Set X} (S : Set (C → C)) : Set C :=
  {x | ∀ T ∈ S, T x = x}

/-- Theorem 1.1. -/
theorem reading_thm_1_1
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X)
    (C : Set X) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbdd : Bornology.IsBounded C) (hconv : Convex ℝ C)
    (F : C → C) (hF : Nonexpansive F) :
    ∃ x : C, F x = x := sorry

/-- Corollary 1.2 (commuting families). -/
theorem reading_cor_1_2
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X)
    (C : Set X) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbdd : Bornology.IsBounded C) (hconv : Convex ℝ C)
    (S : Set (C → C))
    (hcomm : ∀ T ∈ S, ∀ T' ∈ S, T ∘ T' = T' ∘ T)
    (hne_maps : ∀ T ∈ S, Nonexpansive T) :
    (commonFix S).Nonempty ∧
      ∃ R : C → C, (∀ x, R x ∈ commonFix S) ∧ Nonexpansive R ∧
        ∀ x ∈ commonFix S, R x = x := sorry

end ReaderA

/-
Ambiguities and choices (Reader A):

1. "Reflexive": defined as surjectivity of `NormedSpace.inclusionInDoubleDual ℝ X : X →L[ℝ]
   StrongDual ℝ (StrongDual ℝ X)` (the canonical map into the continuous bidual). This is the
   standard definition; it is purely algebraic/surjective, isometry of the map being automatic
   (Hahn–Banach). Not Mathlib's typeclass (none is used); written by hand.
2. "Real Banach space": `NormedAddCommGroup X`, `NormedSpace ℝ X`, `CompleteSpace X`.
   (Reflexive spaces are automatically complete, so `CompleteSpace` is redundant but literal.)
3. "Norm closed": `IsClosed C` in the norm topology of `X` (the only topology on `X` here).
   "Bounded": `Bornology.IsBounded C` (metric boundedness). "Convex": `Convex ℝ C`.
4. `F : C → C` is taken literally as a function on the subtype `C`; nonexpansiveness is
   `‖F a - F b‖ ≤ ‖a - b‖` for all `a b ∈ C`, measured in the given norm. No continuity is
   assumed separately (it follows). Fixed point: `∃ x : C, F x = x` (subtype equality, i.e.
   equality in `X`).
5. Corollary: "pairwise commuting family" read as `T ∘ T' = T' ∘ T` for all `T, T' ∈ S`
   (including T = T', which is trivial). The family `S` is an arbitrary set of selfmaps of C
   (possibly empty, possibly uncountable), as the source's proof treats the empty family.
   `Fix(S)` is a subset of `C` (as a `Set C`). "Nonexpansive retract": there exists
   `R : C → C` with values in `Fix(S)`, nonexpansive, and identity on `Fix(S)`; I phrase
   `R : C → Fix(S)` as `R : C → C` with range in `Fix(S)`, which is equivalent and keeps the
   nonexpansive predicate uniform. Nonemptiness of `Fix(S)` is stated separately (it also
   follows from the retract since `C` is nonempty).
6. Junk values: none arise (no division, subtraction on ℕ, sSup, etc.).
-/

namespace ReaderB

/-- Reflexive: the canonical embedding into the bidual is surjective. -/
def IsReflexive (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

/-- Nonexpansive self-map of `C` in the norm of `X`. -/
def Nonexpansive {X : Type*} [NormedAddCommGroup X] (C : Set X) (F : C → C) : Prop :=
  ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖

/-- Theorem 1.1. -/
theorem readingMain (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (C : Set X) (hne : C.Nonempty) (hcl : IsClosed C)
    (hb : Bornology.IsBounded C) (hconv : Convex ℝ C) (F : C → C) (hF : Nonexpansive C F) :
    ∃ x : C, F x = x := sorry

/-- Corollary 1.2, family indexed by a set of maps. -/
theorem readingCommuting (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (C : Set X) (hne : C.Nonempty) (hcl : IsClosed C)
    (hb : Bornology.IsBounded C) (hconv : Convex ℝ C)
    (S : Set (C → C)) (hS : ∀ T ∈ S, Nonexpansive C T)
    (hcomm : ∀ T ∈ S, ∀ U ∈ S, T ∘ U = U ∘ T) :
    {x : C | ∀ T ∈ S, T x = x}.Nonempty ∧
    ∃ R : C → C, Nonexpansive C R ∧ (∀ x, ∀ T ∈ S, T (R x) = R x) ∧
      (∀ x : C, (∀ T ∈ S, T x = x) → R x = x) := sorry

end ReaderB

/-
Ambiguities / choices.
* "Reflexive": canonical map X → X** (NormedSpace.inclusionInDoubleDual ℝ X) is surjective.
  Banach: I assume [CompleteSpace X] explicitly (reflexive normed spaces are complete anyway,
  so it is harmless).
* "Real": NormedSpace ℝ X.
* C is a Set X; F : C → C on the subtype; nonexpansive is stated with the norm of X on coercions.
  "bounded" = Bornology.IsBounded; "norm closed" = IsClosed; convex = Convex ℝ.
* Corollary: family given as a Set of maps (possibly empty, in which case the retract is id; the
  statement covers it). Pairwise commuting: T ∘ U = U ∘ T for all T, U in S (includes T=U, trivially).
* Retract R : C → Fix(S) is stated as R : C → C with range in Fix (∀ T∈S, T (R x) = R x), R nonexpansive,
  and R identity on Fix. Equivalent to a map into the subtype.
* Junk avoided: no subtraction in ℕ, no division, no sSup; fixed point is an element of C itself.
-/

namespace ReaderC

/-- Reflexivity: the canonical embedding of `X` into its bidual `X**` is surjective. -/
def IsReflexiveSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

/-- `F : C → C` is nonexpansive in the norm of `X`. -/
def NonexpansiveOn {X : Type*} [NormedAddCommGroup X] (C : Set X) (F : C → C) : Prop :=
  ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖

/-- Theorem 1.1: every nonexpansive self-map of a nonempty, norm closed, bounded, convex subset
of a real reflexive Banach space has a fixed point. -/
theorem reading_fixedpoint_thm1 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hX : IsReflexiveSpace X) (C : Set X) (hne : C.Nonempty) (hcl : IsClosed C)
    (hb : Bornology.IsBounded C) (hconv : Convex ℝ C) (F : C → C)
    (hF : NonexpansiveOn C F) : ∃ x : C, F x = x := by
  sorry

/-- The common fixed set of a family `S` of self-maps of `C`. -/
def commonFixSet {X : Type*} [NormedAddCommGroup X] (C : Set X) (S : Set (C → C)) : Set C :=
  {x : C | ∀ T ∈ S, T x = x}

/-- Corollary 1.2: for a pairwise commuting family of nonexpansive self-maps of such a `C`,
the common fixed set is nonempty and is a nonexpansive retract of `C`: there is a nonexpansive
`R : C → C` with range in the fixed set and `R x = x` on the fixed set. -/
theorem reading_fixedpoint_cor2 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hX : IsReflexiveSpace X) (C : Set X) (hne : C.Nonempty) (hcl : IsClosed C)
    (hb : Bornology.IsBounded C) (hconv : Convex ℝ C) (S : Set (C → C))
    (hS : ∀ T ∈ S, NonexpansiveOn C T)
    (hcomm : ∀ T ∈ S, ∀ U ∈ S, ∀ x : C, T (U x) = U (T x)) :
    (commonFixSet C S).Nonempty ∧
      ∃ R : C → C, (∀ x : C, R x ∈ commonFixSet C S) ∧
        (∀ x ∈ commonFixSet C S, R x = x) ∧ NonexpansiveOn C R := by
  sorry

end ReaderC

/-
Comment block: ambiguities and choices.

1. "Reflexive": defined as surjectivity of the canonical embedding X → X** (Mathlib's
   `NormedSpace.inclusionInDoubleDual ℝ X`), the standard definition. Not a Mathlib class, so the
   hypothesis is stated explicitly as `hX`.

2. "Nonexpansive in the given norm": `‖F a - F b‖ ≤ ‖a - b‖` with the norm of `X`, for all
   `a, b ∈ C`. Maps are modelled as `F : C → C` on the subtype, as in the source's `F : C → C`,
   so no junk values arise (no division, no subtraction in ℕ, no sSup).

3. "Nonempty, norm closed, bounded, convex": `C.Nonempty`, `IsClosed C` (norm closed in X, which
   is the source's reading), `Bornology.IsBounded C`, `Convex ℝ C`.

4. Corollary: the family is a `Set (C → C)` of maps, each nonexpansive, pairwise commuting
   (`T (U x) = U (T x)` for all `T, U ∈ S`, including T = U, which is harmless). The common fixed
   set `Fix(S) = {x ∈ C | T x = x for all T ∈ S}` is a subset of C. The retract condition is
   formalised as: a nonexpansive `R : C → C` whose values lie in `Fix(S)` and which fixes
   `Fix(S)` pointwise. The source writes `R : C → Fix(S)`; I kept the codomain as C with range in
   Fix(S), which is the same map up to the inclusion. For the empty family, `Fix(S) = C`, which
   is nonempty by hypothesis, and `R = id` works; the statement covers this case without
   special treatment. `Fix` is written as the explicit set `commonFixSet`, not a Mathlib
   object.

5. Distance on C: the source's nonexpansiveness is in the norm of X, so `NonexpansiveOn` uses
   the subspace metric inherited from X, not a separate metric on C.
-/
