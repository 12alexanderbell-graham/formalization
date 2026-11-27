import Mathlib

/-!
Blind reading (reader A) of O58, "An algebra of infinite little finitistic dimension":
Theorem 1.1 and Corollary 1.2 of the introduction.

Projective dimension is Mathlib's Ext-based notion `CategoryTheory.HasProjectiveDimensionLT`
(`pd X < n` iff `Ext^i(X, -) = 0` for all `i ≥ n`), used only through these `Prop`s, never
through the `WithBot ℕ∞`-valued `projectiveDimension` (so no `⊤`/`⊥` conventions are used).
Left `R`-modules are objects of `ModuleCat.{0} R`; right `R`-modules are left `Rᵐᵒᵖ`-modules.
-/

namespace ReaderA

open CategoryTheory

section Defs

variable (R : Type) [Ring R]

/-- `pd_R N < ∞`. -/
def FinitePD (N : ModuleCat.{0} R) : Prop :=
  ∃ n : ℕ, HasProjectiveDimensionLE N n

/-- `findim R = ∞` (little finitistic dimension, left modules): the supremum of `pd_R N`
over finitely generated left `R`-modules `N` with `pd_R N < ∞` is infinite, i.e. for every
`n` there is such an `N` with `pd_R N > n`. -/
def LittleFindimInfinite : Prop :=
  ∀ n : ℕ, ∃ N : ModuleCat.{0} R,
    Module.Finite R N ∧ FinitePD R N ∧ ¬ HasProjectiveDimensionLE N n

/-- `Findim R = ∞` (big finitistic dimension, all left modules). -/
def BigFindimInfinite : Prop :=
  ∀ n : ℕ, ∃ N : ModuleCat.{0} R, FinitePD R N ∧ ¬ HasProjectiveDimensionLE N n

/-- `findim R = d` for a natural number `d`: every finitely generated left module of finite
projective dimension has `pd ≤ d`, and the supremum `d` is attained (some finitely generated
`N` has `pd N ≤ d` and `¬ pd N < d`, i.e. `pd N = d`). -/
def LittleFindimEq (d : ℕ) : Prop :=
  (∀ N : ModuleCat.{0} R, Module.Finite R N → FinitePD R N → HasProjectiveDimensionLE N d) ∧
  ∃ N : ModuleCat.{0} R, Module.Finite R N ∧
    HasProjectiveDimensionLE N d ∧ ¬ HasProjectiveDimensionLT N d

/-- `Findim R = d` for a natural number `d` (all left modules). -/
def BigFindimEq (d : ℕ) : Prop :=
  (∀ N : ModuleCat.{0} R, FinitePD R N → HasProjectiveDimensionLE N d) ∧
  ∃ N : ModuleCat.{0} R, HasProjectiveDimensionLE N d ∧ ¬ HasProjectiveDimensionLT N d

/-- "Injective left `R`-modules generate": the smallest triangulated subcategory of the
unbounded derived category `D(R-Mod)` that contains the injective left modules (as complexes
concentrated in degree `0`) and is closed under arbitrary coproducts is the whole category.
Equivalently: every such (isomorphism-closed) subcategory contains every object. -/
noncomputable def InjectivesGenerate : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{0} R)
  ∀ P : ObjectProperty (DerivedCategory (ModuleCat.{0} R)),
    P.IsTriangulated → P.IsClosedUnderIsomorphisms →
    (∀ ι : Type, P.IsClosedUnderColimitsOfShape (Discrete ι)) →
    (∀ I : ModuleCat.{0} R, Injective I → P ((DerivedCategory.singleFunctor _ 0).obj I)) →
    ∀ X, P X

end Defs

/-- **Theorem 1.1.** There is a finite-dimensional unital complex algebra `A` such that, for
every integer `m ≥ 1`, there is a finite-dimensional left `A`-module `N_m` with
`2m - 2 ≤ pd_A N_m < ∞`. In particular, `findim A = ∞`.

`2m - 2 ≤ pd N` is written `¬ (pd N < i)` for the natural number `i` with `i + 2 = 2m`. -/
theorem reading_thm_1_1 :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A), FiniteDimensional ℂ A ∧
      (∀ m : ℕ, 1 ≤ m → ∃ N : ModuleCat.{0} A,
        Module.Finite ℂ (RestrictScalars ℂ A N) ∧
        (∀ i : ℕ, i + 2 = 2 * m → ¬ HasProjectiveDimensionLT N i) ∧
        FinitePD A N) ∧
      LittleFindimInfinite A := sorry

/-- **Corollary 1.2 (Extreme left–right asymmetry).** There is a finite-dimensional unital
complex algebra `Λ` with `findim Λ = Findim Λ = ∞` and `findim Λᵒᵖ = Findim Λᵒᵖ = 0` (all
four using left modules); injective left `Λ`-modules do not generate `D(Λ-Mod)`, whereas
injective right `Λ`-modules (= left `Λᵒᵖ`-modules) generate `D(Mod-Λ)`. -/
theorem reading_cor_1_2 :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ), FiniteDimensional ℂ Λ ∧
      LittleFindimInfinite Λ ∧ BigFindimInfinite Λ ∧
      LittleFindimEq Λᵐᵒᵖ 0 ∧ BigFindimEq Λᵐᵒᵖ 0 ∧
      ¬ InjectivesGenerate Λ ∧ InjectivesGenerate Λᵐᵒᵖ := sorry

end ReaderA

/-
Ambiguities and choices (reader A)
==================================

1. Projective dimension. The text uses `pd_A N` without defining it. I used Mathlib's
   Ext-vanishing notion `HasProjectiveDimensionLT N n` ("pd N < n") and its abbreviation
   `HasProjectiveDimensionLE N n` ("pd N ≤ n"), which for module categories agrees with the
   length of a shortest projective resolution. I never use the `WithBot ℕ∞`-valued
   `projectiveDimension`, so no `⊤`/`⊥` junk enters: "pd N < ∞" is `∃ n, pd N ≤ n`,
   "pd N ≥ j" is `¬ pd N < j`, "pd N > n" is `¬ pd N ≤ n`.

2. `2m - 2 ≤ pd_A N_m`. To avoid ℕ subtraction, it is written as
   `∀ i, i + 2 = 2 * m → ¬ HasProjectiveDimensionLT N i` (for `m ≥ 1` the only such `i` is
   `2m - 2`). Convention issue for `m = 1`: "0 ≤ pd N" is vacuous if `pd 0 = 0`, but with
   Mathlib's convention (`pd 0 = -∞`, i.e. `HasProjectiveDimensionLT 0 0`) it forces
   `N_1 ≠ 0`. I kept Mathlib's convention (slightly stronger; harmless, since one may take
   `N_1 = A`).

3. Finitistic dimensions as suprema. To avoid `sSup`/`iSup` junk (empty or unbounded sets in
   ℕ∞ / WithBot ℕ∞), the two statements "dim = ∞" and "dim = 0" are expressed directly:
   - `findim R = ∞`: for every `n` there is a finitely generated `N` with `pd N < ∞` and
     `pd N > n` (the supremum is unbounded).
   - `findim R = d` (`d : ℕ`): all f.g. `N` of finite pd have `pd N ≤ d`, AND some f.g. `N`
     has `pd N = d` (a supremum of a nonempty bounded set of naturals is attained). For
     `d = 0` the second clause means a nonzero projective f.g. module exists (e.g. `R` itself
     when `R ≠ 0`); this matches the supremum being 0 rather than `-∞`.
   The big versions drop `Module.Finite`.

4. Universe of "all left modules". Modules live in `ModuleCat.{0} R` (carriers in `Type`, the
   same universe as the algebra). "All left modules" in the big finitistic dimension and in the
   derived category is read as all modules in this universe. This is a choice: for the `= 0`
   statement, restricting to one universe is a priori weaker than quantifying over all
   universes; for the `= ∞` statements it is a priori stronger.

5. "Finite-dimensional left A-module" (Theorem 1.1): `Module.Finite ℂ (RestrictScalars ℂ A N)`,
   i.e. finite-dimensional over ℂ via the algebra map. "Finitely generated" (in the definition
   of findim): `Module.Finite A N`. For a finite-dimensional algebra these coincide.

6. "Finite-dimensional unital complex algebra": a type with `Ring` (associative, unital),
   `Algebra ℂ`, and `FiniteDimensional ℂ`. Commutativity is not assumed.

7. Opposite algebra. `Λ^op` is `Λᵐᵒᵖ` (`MulOpposite`), with its induced `Ring` and `Algebra ℂ`
   structures. "All four dimensions here use left modules": `findim(Λ^op)` is computed with
   left `Λᵐᵒᵖ`-modules (= right `Λ`-modules). "Injective right Λ-modules generate the derived
   category of right Λ-modules" is `InjectivesGenerate Λᵐᵒᵖ`.

8. Injective generation. "Smallest triangulated subcategory ... containing [the injectives]
   and closed under arbitrary coproducts is the whole category" is expressed as: every
   `P : ObjectProperty (D(R-Mod))` that is triangulated (`ObjectProperty.IsTriangulated`:
   contains 0, stable under shifts, closed under extensions in distinguished triangles),
   closed under isomorphisms, closed under coproducts indexed by any `ι : Type`, and contains
   every injective module placed in degree 0, contains every object. (Smallest such
   subcategory = intersection of all of them.) Choices: triangulated subcategories are taken
   isomorphism-closed ("strictly full"), the standard convention; "arbitrary coproducts" means
   coproducts indexed by small (`Type`) index sets, which is what exists in `D(R-Mod)` for
   modules in `Type`; the derived category model is `HasDerivedCategory.standard` (any model
   gives an equivalent category, so the property does not depend on this choice); an
   injective module is identified with its image under `DerivedCategory.singleFunctor _ 0`.

9. Theorem 1.1's "In particular, findim A = ∞" is stated as a separate conjunct
   (`LittleFindimInfinite A`) even though it follows from the first conjunct together with
   `N_m` being finitely generated; this is the literal reading.

10. Not stated: the consequences in the running text that are not part of Theorem 1.1 /
    Corollary 1.2 (big finitistic dimension of `A` infinite, Artin-algebra remark, Rickard's
    theorem applied to `A`), and the companion characteristic-two result. The proof of the
    corollary via Cummings' triangular algebra is not formalized.
-/
