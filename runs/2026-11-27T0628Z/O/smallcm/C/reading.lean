import Mathlib

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
