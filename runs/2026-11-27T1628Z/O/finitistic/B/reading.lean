import Mathlib

namespace ReaderB

open CategoryTheory Abelian

universe u

/-- Finitistic dimension (over left modules) of `A` is at most `n` on finitely generated modules:
every f.g. left `A`-module of finite projective dimension has projective dimension `≤ n`. -/
def LittleFindimLE (A : Type) [Ring A] (n : ℕ) : Prop :=
  ∀ N : ModuleCat.{0} A, Module.Finite A N → (∃ m : ℕ, HasProjectiveDimensionLE N m) →
    HasProjectiveDimensionLE N n

/-- Same for all left modules. -/
def BigFindimLE (A : Type) [Ring A] (n : ℕ) : Prop :=
  ∀ N : ModuleCat.{0} A, (∃ m : ℕ, HasProjectiveDimensionLE N m) →
    HasProjectiveDimensionLE N n

/-- `findim A = ∞`: not bounded by any natural number. -/
def LittleFindimInfinite (A : Type) [Ring A] : Prop := ∀ n : ℕ, ¬ LittleFindimLE A n

def BigFindimInfinite (A : Type) [Ring A] : Prop := ∀ n : ℕ, ¬ BigFindimLE A n

/-- `findim A = 0`. -/
def LittleFindimZero (A : Type) [Ring A] : Prop := LittleFindimLE A 0

def BigFindimZero (A : Type) [Ring A] : Prop := BigFindimLE A 0

/-- Injective left `A`-modules generate: the only subcategory of the unbounded derived category of
`ModuleCat A` that is triangulated, closed under isomorphisms and arbitrary (small) coproducts,
and contains the injectives is everything. -/
def InjectivesGenerate (A : Type) [Ring A] : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{0} A)
  ∀ P : ObjectProperty (DerivedCategory (ModuleCat.{0} A)),
    P.IsClosedUnderIsomorphisms → P.IsTriangulated →
    (∀ J : Type, P.IsClosedUnderColimitsOfShape (Discrete J)) →
    (∀ I : ModuleCat.{0} A, Injective I → P ((DerivedCategory.singleFunctor _ 0).obj I)) →
    P = ⊤

/-- Theorem 1.1. -/
theorem readingTheorem11 :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A) (_ : Module.Finite ℂ A),
      (∀ m : ℕ, 1 ≤ m → ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
        (∃ j : ℕ, j + 2 = 2 * m ∧ ¬ HasProjectiveDimensionLT N j) ∧
        ∃ n : ℕ, HasProjectiveDimensionLE N n) ∧
      LittleFindimInfinite A := sorry

/-- Corollary 1.2. -/
theorem readingCorollary12 :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ) (_ : Module.Finite ℂ Λ),
      LittleFindimInfinite Λ ∧ BigFindimInfinite Λ ∧
      LittleFindimZero Λᵐᵒᵖ ∧ BigFindimZero Λᵐᵒᵖ ∧
      ¬ InjectivesGenerate Λ ∧ InjectivesGenerate Λᵐᵒᵖ := sorry

end ReaderB

/-
Ambiguities and choices.
* Dimensions as ℕ∞/sup avoided: "findim A = ∞" is "for no n is every f.g. finite-pd module of pd ≤ n"
  (LittleFindimInfinite); "= 0" is "every such module has pd ≤ 0" (projective). This is equivalent to the
  sup definition (sup of a set of ℕ is ∞ iff unbounded; the set is nonempty since projectives have pd 0,
  and sup = 0 iff all pd ≤ 0), with no sSup, ⊤ or ⊥ in the statement. Mathlib's WithBot ℕ∞
  `projectiveDimension` is not used.
* pd N < ∞ is `∃ m, HasProjectiveDimensionLE N m` (Ext vanishes above m). pd N ≥ 2m-2 is encoded as
  `∃ j, j + 2 = 2*m ∧ ¬ HasProjectiveDimensionLT N j` (pd ≥ j iff not pd < j), avoiding ℕ subtraction.
  For m ≥ 1, j = 2m-2 ≥ 0 exactly. (N=0 is not an issue: pd 0-object would be LT 0, and j=0 allows
  ¬LT 0 meaning N nonzero, a harmless strengthening at m = 1 that is implied by pd N >= 0 for real modules.)
* "finite-dimensional unital complex algebra": a Type A with Ring, Algebra ℂ, Module.Finite ℂ (types in Type 0;
  existential over the algebra data, with instances as existential witnesses; Λ renamed identifier `Λ` fine).
* Left A-modules: ModuleCat.{0} A. "Finite-dimensional left A-module" = Module.Finite A N (f.g. over A; equals finite-dim over ℂ since A is finite-dim,
  and Lean has no direct `Module ℂ N` instance on a ModuleCat A object, so ℂ-dimension is not used).
* Λᵐᵒᵖ is the opposite algebra; its left modules are right Λ-modules.
* Generation: "smallest triangulated subcategory of D(all left modules) closed under coproducts containing
  injectives is everything" is formalized as: any ObjectProperty closed under isos, triangulated, closed
  under all small coproducts (colimits of shape Discrete J, J : Type) and containing injectives is ⊤.
  Uses Mathlib's standard derived category (HasDerivedCategory.standard).
* The two "injective-generation sentences" of Corollary 1.2 are the last two conjuncts. The algebra
  statement in Theorem 1.1 deduces nothing about injective generation, so not included.
* Both Λ-existential statements are in one theorem (same Λ for all six properties), as the text says.
-/
