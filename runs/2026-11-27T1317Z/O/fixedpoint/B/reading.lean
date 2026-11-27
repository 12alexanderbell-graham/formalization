import Mathlib

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
