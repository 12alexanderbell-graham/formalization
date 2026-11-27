import Mathlib

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
