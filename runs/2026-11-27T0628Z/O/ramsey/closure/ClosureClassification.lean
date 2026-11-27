import Mathlib
import Readings.Ramsey
import ComparatorChallenges.EuclideanRamsey

/-! # Target O, family O21: reader B's Classification against the family's headline challenge
`EuclideanRamsey.classification` (run 2026-11-27T0628Z; this challenge was first missed — EXTERNAL_O.md, Correction).
Frozen statement taken with `type_of%`: for s ≥ 2 distinct points a with affine span ℝ^d (and 1 ≤ d), `Ramsey a ↔
FieldCriterion a`, the criterion over F ⊗_ℚ F with F = ℚ(coordinates) (`IntermediateField.adjoin`), the matrix
indexed by `Option (Fin d)` (none = the constant coordinate). Reader B's criterion is the same with the matrix
indexed by `Fin (d + 1)` (0 = the constant coordinate, `Fin.cons`): carried by `finSuccEquiv d`; B's Ramsey set
property is the frozen enumeration property (`toSet`/`ofSet`); 1 ≤ d follows from two distinct points. Readers A
(F written as the adjunction of a set equal to the frozen one, but a different term) and C (F as a `Subfield ℝ`)
are not closed here: their tensor rings are isomorphic to the frozen one, not equal, and the transport is not
written this run. -/

namespace TargetO.Ramsey

open OAI.EuclideanRamsey

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The common shape of the readers' Ramsey property (after `A.Finite ∧ A.Nonempty`). -/
def SetRamsey {d : ℕ} (A : Set (E d)) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧ ∀ c : E D → Fin r, ∃ f : E d → E D,
    (∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y) ∧ ∃ k : Fin r, ∀ x ∈ A, c (f x) = k

/-- A finite set has an injective enumeration. -/
theorem enum {d : ℕ} {A : Set (E d)} (hA : A.Finite) :
    ∃ (s : ℕ) (a : Fin s → E d), Function.Injective a ∧ Set.range a = A ∧ s = hA.toFinset.card := by
  classical
  let e := hA.toFinset.equivFin
  refine ⟨_, fun i => (e.symm i).1, fun i j h => e.symm.injective (Subtype.ext h), ?_, rfl⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩; exact (Set.Finite.mem_toFinset hA).mp (e.symm i).2
  · intro hx
    exact ⟨e ⟨x, (Set.Finite.mem_toFinset hA).mpr hx⟩, by simp⟩

theorem ofSet {d s : ℕ} {A : Set (E d)} {a : Fin s → E d} (hr : Set.range a ⊆ A) (h : SetRamsey A) :
    Ramsey a := by
  intro r hr2
  obtain ⟨D, hD, hc⟩ := h r hr2
  refine ⟨D, hD, fun c => ?_⟩
  obtain ⟨f, hf, k, hk⟩ := hc c
  exact ⟨fun i => f (a i), fun i j => hf _ (hr ⟨i, rfl⟩) _ (hr ⟨j, rfl⟩), k,
    fun i => hk _ (hr ⟨i, rfl⟩)⟩

theorem toSet {d s : ℕ} {A : Set (E d)} {a : Fin s → E d} (ha : Function.Injective a)
    (hr : Set.range a = A) (h : Ramsey a) : SetRamsey A := by
  classical
  intro r hr2
  obtain ⟨D, hD, hc⟩ := h r hr2
  refine ⟨D, hD, fun c => ?_⟩
  obtain ⟨b, hb, k, hk⟩ := hc c
  let f : E d → E D := fun x => if hx : ∃ i, a i = x then b hx.choose else 0
  have hfa : ∀ i, f (a i) = b i := by
    intro i
    have hx : ∃ j, a j = a i := ⟨i, rfl⟩
    simp only [f, dif_pos hx]
    rw [ha hx.choose_spec]
  refine ⟨f, ?_, k, ?_⟩
  · rintro x hx y hy
    rw [← hr] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    rw [hfa, hfa]; exact hb i j
  · rintro x hx
    rw [← hr] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hfa]; exact hk i


theorem B_crit {s d : ℕ} (a : Fin s → E d) :
    ReaderB.HasTensorMatrix a ↔ FieldCriterion a := by
  have hp : ∀ i k, ReaderB.pvec a i k = augmented a i (finSuccEquiv d k) := by
    intro i k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [finSuccEquiv_zero]; rfl
    · rw [finSuccEquiv_succ]; rfl
  constructor
  · rintro ⟨P, h1, h2⟩
    refine ⟨fun α β => P ((finSuccEquiv d).symm α) ((finSuccEquiv d).symm β), fun i => ?_, fun α β => ?_⟩
    · refine Eq.trans ?_ (h1 i)
      symm
      refine Fintype.sum_equiv (finSuccEquiv d) _ _ fun k => ?_
      refine Fintype.sum_equiv (finSuccEquiv d) _ _ fun l => ?_
      simp only [Equiv.symm_apply_apply]
      rw [hp, hp]
      rfl
    · have e1 : (finSuccEquiv d).symm (some α) = α.succ := by
        rw [Equiv.symm_apply_eq, finSuccEquiv_succ]
      have e2 : (finSuccEquiv d).symm (some β) = β.succ := by
        rw [Equiv.symm_apply_eq, finSuccEquiv_succ]
      show multiply a (P ((finSuccEquiv d).symm (some α)) ((finSuccEquiv d).symm (some β))) = _
      rw [e1, e2]
      exact h2 α β
  · rintro ⟨P, h1, h2⟩
    refine ⟨fun k l => P (finSuccEquiv d k) (finSuccEquiv d l), fun i => ?_, fun α β => ?_⟩
    · refine Eq.trans ?_ (h1 i)
      refine Fintype.sum_equiv (finSuccEquiv d) _ _ fun k => ?_
      refine Fintype.sum_equiv (finSuccEquiv d) _ _ fun l => ?_
      rw [hp, hp]
      rfl
    · show multiply a (P (finSuccEquiv d α.succ) (finSuccEquiv d β.succ)) = _
      rw [finSuccEquiv_succ, finSuccEquiv_succ]
      exact h2 α β

theorem B_classification : (type_of% @OAI.EuclideanRamsey.classification) →
    (type_of% @ReaderB.readingClassification) := by
  intro h s d a hinj hs hspan
  have hd : 1 ≤ d := by
    by_contra hd0
    have : d = 0 := by omega
    subst this
    have h01 : (⟨0, by omega⟩ : Fin s) ≠ ⟨1, by omega⟩ := by simp
    exact h01 (hinj (Subsingleton.elim _ _))
  refine Iff.trans ?_ ((h a hs hd hinj hspan).trans (B_crit a).symm)
  have hfin : (Set.range a).Finite := Set.finite_range a
  have hne : (Set.range a).Nonempty := ⟨a ⟨0, by omega⟩, ⟨_, rfl⟩⟩
  constructor
  · rintro ⟨-, -, hR⟩; exact ofSet le_rfl hR
  · intro hR; exact ⟨hfin, hne, toSet hinj rfl hR⟩

end TargetO.Ramsey

#print axioms TargetO.Ramsey.B_classification
