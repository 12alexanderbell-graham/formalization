import Mathlib

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
