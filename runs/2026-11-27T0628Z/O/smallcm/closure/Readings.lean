import Mathlib

namespace ReaderA

/-!
# Blind reading (reader A), family O7 "smallcm"

Source: `smallcm/sources/paper_lines30-70.tex` (abstract, Introduction, Theorem 1.1 = `thm:main`).

Source definitions used:
* "A small Cohen–Macaulay module over a Noetherian local ring (R, 𝔪) is a nonzero finitely
  generated R-module M such that depth_R M = dim R."
* "The domain form of the small Cohen–Macaulay module conjecture asks whether every complete
  Noetherian local domain has one."
-/

open IsLocalRing

namespace ReadingA.SmallCM

/-- `rs` is an `M`-regular sequence contained in the maximal ideal: every entry lies in `𝔪`,
each `rᵢ` is a non-zero-divisor on `M ⧸ (r₁,…,rᵢ₋₁)M`, and `M ≠ (r₁,…,rₙ)M`
(Mathlib's `RingTheory.Sequence.IsRegular`). -/
def IsMaxIdealRegSeq (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (rs : List R) : Prop :=
  (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ RingTheory.Sequence.IsRegular M rs

/-- Own definition of depth (written by the reader, not Mathlib's `IsLocalRing.depth`):
`HasDepth R M n` means `depth_R M = n`, i.e. the supremum of the lengths of `M`-regular
sequences in `𝔪` is exactly `n`. Stated as "some regular sequence in `𝔪` has length `n` and
every regular sequence in `𝔪` has length `≤ n`", so no `sSup` (and no junk value) is used. -/
def HasDepth (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  (∃ rs : List R, rs.length = n ∧ IsMaxIdealRegSeq R M rs) ∧
    ∀ rs : List R, IsMaxIdealRegSeq R M rs → rs.length ≤ n

/-- "small Cohen–Macaulay module" = nonzero finitely generated `M` with `depth_R M = dim R`.
`dim R` is Mathlib's `ringKrullDim R : WithBot ℕ∞`; equality with a natural number `n`
also records that the Krull dimension is finite. -/
def IsSmallCM (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Nontrivial M ∧ ∃ n : ℕ, ringKrullDim R = n ∧ HasDepth R M n

/-- The domain form of the small Cohen–Macaulay module conjecture, as the source states it:
every complete Noetherian local domain has a small Cohen–Macaulay module.
"complete" = `𝔪`-adically complete and separated (`IsAdicComplete (maximalIdeal R) R`). -/
def SmallCMDomainConjecture : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (maximalIdeal R) R →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M), IsSmallCM R M

/-- Theorem 1.1 (`thm:main`): there exists a three-dimensional complete Noetherian normal
local domain `R` containing `ℂ`, with residue field `ℂ`, such that no nonzero finitely generated
`R`-module has depth three. -/
theorem readingSmallCM_main :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
      (_ : IsNoetherianRing R) (_ : Algebra ℂ R),
      ringKrullDim R = 3 ∧
      IsAdicComplete (maximalIdeal R) R ∧
      IsIntegrallyClosed R ∧
      Function.Bijective ((residue R).comp (algebraMap ℂ R)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module R M],
        Module.Finite R M → Nontrivial M → ¬ HasDepth R M 3 := by
  sorry

/-- Abstract: "This disproves the domain form of the small Cohen–Macaulay module conjecture." -/
theorem readingSmallCM_disproof : ¬ SmallCMDomainConjecture := by
  sorry

/-- Cross-check variant of Theorem 1.1 using Mathlib's (Ext-based) `IsLocalRing.depth` instead
of the reader's regular-sequence definition. Not the primary reading. -/
theorem readingSmallCM_main_mathlibDepth :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
      (_ : IsNoetherianRing R) (_ : Algebra ℂ R),
      ringKrullDim R = 3 ∧
      IsAdicComplete (maximalIdeal R) R ∧
      IsIntegrallyClosed R ∧
      Function.Bijective ((residue R).comp (algebraMap ℂ R)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module R M],
        Module.Finite R M → Nontrivial M → IsLocalRing.depth (ModuleCat.of R M) ≠ 3 := by
  sorry

end ReadingA.SmallCM

/-!
## Ambiguities and choices

1. **Depth.** Written by me (`HasDepth`) via `𝔪`-regular sequences (Mathlib's
   `RingTheory.Sequence.IsRegular`, which includes `M ≠ (rs)M`), as "max length = n" rather than
   `sSup`, so there is no junk value. For `M = 0` no sequence is regular, so `HasDepth R 0 n` is
   false for every `n`; the theorem only quantifies over nonzero `M` anyway. Mathlib has had an
   Ext-based `IsLocalRing.depth : ModuleCat R → ℕ∞` since 2026 (it is `⊤` on `0`, and a `sSup`
   in the complete lattice `ℕ∞`, so not junk); it agrees with the regular-sequence depth for
   nonzero finitely generated modules over a Noetherian local ring (Rees). It appears only in the
   cross-check variant `readingSmallCM_main_mathlibDepth`.
   A regular sequence of length ≥ 4 has a regular prefix of length 4, so "not depth 3" is
   correctly captured even though `HasDepth` only bounds lengths by `n`.
2. **"complete"** read as `IsAdicComplete (maximalIdeal R) R` (Hausdorff + complete in the
   `𝔪`-adic topology), the standard meaning for Noetherian local rings.
3. **"three-dimensional"** = Krull dimension: `ringKrullDim R = 3`.
4. **"normal"**: for a domain this means integrally closed in its fraction field:
   `IsIntegrallyClosed R`.
5. **"containing ℂ"**: an `Algebra ℂ R` structure (any ring map from a field to a nonzero ring is
   injective, so this is a subring copy of ℂ).
6. **"with residue field ℂ"**: read as "the composite ℂ → R → R/𝔪 is bijective" (ℂ is a
   coefficient field). Alternative weaker reading: `Nonempty (ResidueField R ≃+* ℂ)` (abstract
   isomorphism); I chose the stronger, natural one since the source says R contains ℂ.
7. **Universes.** R and M are taken in `Type`. Every finitely generated module is isomorphic to
   one in `Type` (a quotient of `Rⁿ`), so nothing is lost. The conjecture is stated for
   `R : Type`; its negation for `Type` is what the counterexample gives (and implies the negation
   of any universe-polymorphic form).
8. **Abstract vs Theorem 1.1.** The abstract says "no nonzero finitely generated maximal
   Cohen–Macaulay module"; Theorem 1.1 says "no nonzero finitely generated R-module has depth
   three". These coincide because dim R = 3. The second theorem is stated as the literal negation
   of the conjecture as defined in the introduction ("every complete Noetherian local domain has
   [a small CM module]").
9. No ℕ subtraction, `tsum`, rpow or unbounded `sSup` is used.

## Proved vs stated
* Theorem 1.1 is the paper's main result ("We prove the following negative answer"); the excerpt
  contains only the statement, not the proof.
* "Disproves the domain form of the conjecture" (abstract) is an immediate consequence of
  Theorem 1.1 (the R of Theorem 1.1 is a complete Noetherian local domain of dimension 3 with no
  small CM module); it is not separately stated as a theorem in the excerpt.
* The remarks on dimensions ≤ 2 (finite normalization is CM, cited to Hochster 2017) and the
  graded results (Hartshorne, Peskine–Szpiro, Hochster) are cited background, not claims of the
  paper, and are not formalized.
-/
end ReaderA

namespace ReaderB

open IsLocalRing

namespace ReadingO7B

/-- depth_R M for a module over a local ring: supremum of lengths of M-regular sequences
(Mathlib `RingTheory.IsRegular`) with entries in the maximal ideal. Valued in ℕ∞, so no junk:
for nonzero M the set is nonempty (empty list), and ⊤ is allowed. -/
noncomputable def depth (R : Type) [CommRing R] [IsLocalRing R]
    (M : Type) [AddCommGroup M] [Module R M] : ℕ∞ :=
  ⨆ (rs : {l : List R // (∀ r ∈ l, r ∈ maximalIdeal R) ∧ RingTheory.Sequence.IsRegular M l}),
    (rs.1.length : ℕ∞)

/-- The domain form of the small CM module conjecture: every complete Noetherian local domain
has a nonzero finitely generated module of depth = dim R. -/
def SmallCMDomainConjecture : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R],
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M), Module.Finite R M ∧ Nontrivial M ∧
      ((depth R M : ℕ∞) : WithBot ℕ∞) = ringKrullDim R

/-- Theorem 1.1. -/
theorem reading_thm_1_1 :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (_ : IsNoetherianRing R)
      (_ : Algebra ℂ R),
      IsAdicComplete (maximalIdeal R) R ∧ IsIntegrallyClosed R ∧ ringKrullDim R = 3 ∧
      Function.Bijective ((residue R).comp (algebraMap ℂ R)) ∧
      ∀ (M : Type) (_ : AddCommGroup M) (_ : Module R M), Module.Finite R M → Nontrivial M →
        depth R M ≠ 3 := sorry

/-- Abstract: disproves the domain form of the conjecture. -/
theorem reading_disproves_conjecture : ¬ SmallCMDomainConjecture := sorry

end ReadingO7B

/-
Ambiguities / choices (reader B):
* Depth: Mathlib has no depth. I define it as sup (in ℕ∞) of lengths of M-regular sequences
  (Mathlib's IsRegular: weakly regular and M/(rs)M ≠ 0) with entries in the maximal ideal. For
  finitely generated M over Noetherian local R this agrees with the usual depth (Ext definition).
  ℕ∞-valued iSup, nonempty index for nonzero M, so no junk. The source never defines depth.
* "Depth three" in Thm 1.1 -> depth R M ≠ 3 for all nonzero f.g. M. ("Nonzero" is explicit in the
  abstract, but Thm 1.1 as stated literally says "no nonzero f.g. module has depth three"; I match.)
* "Normal local domain": IsDomain + IsIntegrallyClosed R (in its fraction ring). Excellent-ness not required.
* "Complete": IsAdicComplete (maximalIdeal R) R. "Containing ℂ": an Algebra ℂ R structure (existential).
  "Residue field ℂ": the composite ℂ → R → R/m is bijective (so ℂ-structure is compatible).
* Three-dimensional: ringKrullDim R = 3 (WithBot ℕ∞).
* Universes: R and M in Type (universe 0); fine since f.g. modules over R:Type are small up to iso.
* Conjecture: as the source states it, "every complete Noetherian local domain has a small CM
  module" = nonzero f.g. M with depth M = dim R; the negation theorem is ¬ of that. The theorem
  reading_disproves_conjecture is a consequence of Thm 1.1 (R with dim 3, no module of depth 3);
  source states it as a corollary in abstract/introduction, proved by Thm 1.1 (statement only in the excerpt).
* Introduction facts about dimension ≤ 2 and graded results are cited, not formalized.
-/
end ReaderB

namespace ReaderC

/-!
Reading C, family O7: "A Complete Local Domain without a Small Cohen–Macaulay Module".

Depth is Mathlib's `IsLocalRing.depth` (Ext-based, `RingTheory/Depth/Basic.lean`); for a
Noetherian local ring and a finitely generated module with `m M ≠ M` this agrees with the
regular-sequence depth used in the source. "Small Cohen–Macaulay module" in the source is a
nonzero finitely generated module M with depth M = dim R; the conjecture is the domain form.
-/

open IsLocalRing

/-- Theorem 1.1 of the source: there is a three-dimensional complete Noetherian normal local
domain R containing ℂ, with residue field ℂ, such that no nonzero finitely generated
R-module has depth three. -/
theorem reading_thm1 :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R)
      (_ : IsDomain R) (_ : IsIntegrallyClosed R) (_ : IsAdicComplete (maximalIdeal R) R)
      (_ : Algebra ℂ R),
      ringKrullDim R = 3 ∧
      Function.Bijective (fun c : ℂ => residue R (algebraMap ℂ R c)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module R M],
        Module.Finite R M → Nontrivial M → IsLocalRing.depth (ModuleCat.of R M) ≠ 3 := by
  sorry

/-- The second claim of the abstract: the negation of the domain form of the small
Cohen–Macaulay module conjecture, i.e. not every complete Noetherian local domain carries a
nonzero finitely generated module M with depth M = dim R. -/
theorem reading_thm2 :
    ¬ (∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
        [IsAdicComplete (maximalIdeal R) R],
        ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M),
          Module.Finite R M ∧ Nontrivial M ∧
          ((IsLocalRing.depth (ModuleCat.of R M) : ℕ∞) : WithBot ℕ∞) = ringKrullDim R) := by
  sorry

/-!
Comments on choices and ambiguities.

* Ambiguity: "no nonzero finitely generated R-module has depth three". Read literally, with
  depth three, not depth equal to dim R. Since dim R = 3 in the theorem, these coincide; the
  literal form is kept in `reading_thm1`.
* "Residue field ℂ" is read as: the composite ℂ → R → R/m is bijective (an isomorphism of
  fields), not merely a field embedding.
* "Containing ℂ" is read as an ℂ-algebra structure on R (the map is automatically injective
  since R is a nonzero domain and ℂ is a field). The `Algebra ℂ R` binder is existentially
  quantified together with R.
* "Complete" is `IsAdicComplete` for the maximal ideal. "Normal" is `IsIntegrallyClosed`
  (in the fraction field), which for a domain is the usual meaning.
* "Three-dimensional" is `ringKrullDim R = 3` (Mathlib's Krull dimension in `WithBot ℕ∞`).
* Depth is Mathlib's `IsLocalRing.depth` of `ModuleCat.of R M` for `M : Type`. The junk
  value issue does not arise here: depth is a `sSup` over ℕ∞ and the claim is only about
  nonzero finitely generated M. For a Subsingleton M, Mathlib gives ⊤, which is excluded by
  `Nontrivial M`.
* `reading_thm2`: the conjecture quantifies over complete Noetherian local domains (no
  containment of ℂ, no residue-field condition), as the source's introduction states. The
  equation `depth = dim R` is cast from ℕ∞ into `WithBot ℕ∞` to match `ringKrullDim`.
* Proved vs stated: the source's Theorem 1.1 is the main result (constructed, so a claim to be
  proved). The negation in `reading_thm2` is the abstract's consequence ("disproves"); it is
  a direct consequence of Theorem 1.1 and the source does not prove it separately in the
  excerpt I read.
* The excerpt I read contains only the introduction (no construction). Nothing in it fixes
  whether "complete" is intended as Mathlib's `IsAdicComplete` or as completeness in the
  m-adic topology; these coincide for Noetherian local rings.
-/
end ReaderC
