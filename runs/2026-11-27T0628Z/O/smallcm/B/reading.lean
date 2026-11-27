import Mathlib

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
