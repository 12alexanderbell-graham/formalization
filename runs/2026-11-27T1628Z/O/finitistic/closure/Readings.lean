import Mathlib

/-! # Target O, family finitistic (O58): the three blind readings of run 2026-11-27T1628Z (brief 5dfa7d5), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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


/-
Blind reading C, target O, family O58 "An algebra of infinite little finitistic dimension".
Source read: abstract and 01-introduction.tex lines 1-112 only.
-/

namespace ReaderC

/-- A finite free resolution of length n of the left A-module M: an exact sequence
0 → P_n → ⋯ → P_0 → M → 0 with P_i = ⊕_{ι i} A free, d i : P_{i+1} → P_i, and e : P_0 → M
surjective, with ker e = im d_0, ker d_i = im d_{i+1}, and P_i = 0 for i > n. -/
def freeResLength (A : Type) [Ring A] (M : Type) [AddCommGroup M] [Module A M] (n : ℕ) : Prop :=
  ∃ (ι : ℕ → Type) (d : ∀ i, (ι (i + 1) →₀ A) →ₗ[A] (ι i →₀ A))
    (e : (ι 0 →₀ A) →ₗ[A] M),
    Function.Surjective e ∧
    LinearMap.ker e = LinearMap.range (d 0) ∧
    (∀ i, LinearMap.ker (d i) = LinearMap.range (d (i + 1))) ∧
    (∀ i, n < i → ∀ x : ι i →₀ A, x = 0)

/-- Projective dimension pd_A M ∈ ℕ∞: the infimum of the lengths n of finite resolutions.
If no finite resolution exists the infimum over the empty set is ⊤ = ∞, which is the
text's "pd = ∞". -/
noncomputable def pdFree (A : Type) [Ring A] (M : Type) [AddCommGroup M] [Module A M] : ℕ∞ :=
  ⨅ (n : ℕ) (_ : freeResLength A M n), (n : ℕ∞)

/-- Little finitistic dimension findim A: the supremum of pd_A N over finitely generated left
A-modules N with pd_A N < ∞. The set is nonempty (A itself, pd 0), so the supremum is
genuine; an unbounded set has supremum ⊤ in ℕ∞, which is the text's ∞. -/
noncomputable def findim (A : Type) [Ring A] : ℕ∞ :=
  sSup {x : ℕ∞ | ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N),
    Module.Finite A N ∧ pdFree A N < ⊤ ∧ x = pdFree A N}

/-- Big finitistic dimension Findim A: as findim, over all left A-modules N with pd_A N < ∞. -/
noncomputable def Findim (A : Type) [Ring A] : ℕ∞ :=
  sSup {x : ℕ∞ | ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N),
    pdFree A N < ⊤ ∧ x = pdFree A N}

/-- Theorem 1.1. There is a finite-dimensional unital complex algebra A such that for every
integer m ≥ 1 there is a finite-dimensional left A-module N_m with 2m - 2 ≤ pd_A N_m < ∞
(written 2m ≤ pd_A N_m + 2 to avoid ℕ subtraction). In particular findim A = ∞. -/
theorem reading_O58_thm1 :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A), FiniteDimensional ℂ A ∧
      (∀ m : ℕ, 1 ≤ m →
        ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module ℂ N)
          (_ : IsScalarTower ℂ A N),
          FiniteDimensional ℂ N ∧
          (2 * (m : ℕ∞)) ≤ pdFree A N + 2 ∧ pdFree A N < ⊤) ∧
      findim A = ⊤ := by
  sorry

/-- Corollary 1.2. There is a finite-dimensional unital complex algebra Λ with
findim Λ = Findim Λ = ∞ and findim Λ^op = Findim Λ^op = 0 (all left modules, Λ^op-left modules
being right Λ-modules). The two injective-generation sentences are NOT formalized; see the
comment block. -/
theorem reading_O58_cor2 :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ), FiniteDimensional ℂ Λ ∧
      findim Λ = ⊤ ∧ Findim Λ = ⊤ ∧
      findim Λᵐᵒᵖ = 0 ∧ Findim Λᵐᵒᵖ = 0 := by
  sorry

end ReaderC

/-
## Comment block: ambiguities and choices (reader C, O58)

1. Projective dimension. The text's pd uses projective resolutions. I define it with free
   resolutions indexed by ι : ℕ → Type, i.e. modules P_i = ⊕_{ι i} A. For a finite resolution,
   pd is the least length, which equals the projective-resolution notion by the standard
   Eilenberg-swindle replacement of projectives by free modules. I did not prove this equivalence;
   it is a choice of definition, flagged here. Projective dimension is ⊤ if no finite
   resolution exists.

2. Universes and types. Modules are taken in Type; ι i and A are Type. Finitely generated means
   Module.Finite A N; finite-dimensional means FiniteDimensional ℂ (ℂ acting through
   IsScalarTower ℂ A N).

3. ℕ∞ and ⊤. The brief asks to avoid ⊤ in ℕ∞-valued quantities. Here ⊤ is not a junk value:
   (a) pd_A N = ⊤ as an infimum over the empty set means "no finite resolution" (the text's ∞);
   (b) findim and Findim are suprema over nonempty sets in the complete lattice ℕ∞, so the
   supremum is ⊤ exactly when the set is unbounded (the text's "fin.dim = ∞"). The comparisons
   "pd < ⊤" express "pd < ∞". The quantity 2m - 2 is written 2m ≤ pd + 2 in ℕ∞, which
   coincides with 2m - 2 ≤ pd for m ≥ 1 and finite pd. No ℕ subtraction appears.

4. Theorem 1.1 quantifiers. "There is a finite-dimensional unital complex algebra A such that for
   every m ≥ 1 there is N_m" is read with A fixed before m (the existential over A is outside the
   ∀ m). N_m is finite-dimensional as a complex vector space, with ℂ acting through A.

5. Big versus little. findim uses only finitely generated N; Findim uses all N with finite pd.
   Both are over left modules. Little ≤ big, so the Findim claim in Cor 1.2 is consistent.

6. Corollary 1.2. Λ is finite-dimensional unital over ℂ. The opposite algebra is Λᵐᵒᵖ with its
   Ring instance; findim Λᵐᵒᵖ and Findim Λᵐᵒᵖ use left Λᵐᵒᵖ-modules, i.e. right Λ-modules, as
   the text says ("All four dimensions here use left modules" for Λ^op). The four values are
   ⊤, ⊤, 0, 0.

7. NOT FORMALIZED: the two injective-generation sentences of Corollary 1.2 (injective left
   Λ-modules do not generate the unbounded derived category of all left Λ-modules; injective
   right Λ-modules generate the unbounded derived category of all right Λ-modules). Reason:
   generation requires the unbounded derived category of all modules, the smallest triangulated
   subcategory closed under arbitrary coproducts, and its closure properties; I did not find a
   usable Mathlib counterpart for the unbounded derived category of all modules and did not
   define one from the text. I did not attempt a partial definition.

8. Not formalized as separate claims: Rickard's theorem and the Cummings/Huisgen-Zimmermann/Igusa-Todorov
   background; the companion characteristic-two algebra; the prose "extreme left-right asymmetry" beyond
   the displayed equalities in Cor 1.2 (which are formalized).

9. Avoided: ℕ subtraction; sSup/sInf of sets I did not check nonempty (both findim sets contain
   pd of A or of any projective-type module, handled as above: findim's set contains pd A for A itself
   as a f.g. free module with pd 0 — the Findim set is nonempty for the same reason); tsum/tprod;
   Nat.nth.

Status: the file is written; compile status is reported in the handback.
-/
