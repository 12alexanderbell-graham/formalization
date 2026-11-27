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
