import Mathlib
import Readings.Ramsey
import ComparatorChallenges.EuclideanRamseyCircle

/-! # Target O, family O21: reader B's five-points-on-a-circle reading against `at_most_five_circle_points_ramsey`
(run 2026-11-27T0628Z). Same `SetRamsey`/`enum`/`toSet` plumbing as `Closure.lean`, here against the circle
challenge's own `Ramsey` (the challenges cannot be imported together). -/

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

theorem B_circle : (type_of% @OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey) →
    (type_of% @ReaderB.readingCircleFive) := by
  intro h A hne hfin hcard c ρ hcirc
  obtain ⟨s, a, ha, hr, hs⟩ := enum hfin
  have hs0 : 0 < s := by
    obtain ⟨x, hx⟩ := hne
    rw [← hr] at hx
    obtain ⟨i, -⟩ := hx
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  have hs5 : s ≤ 5 := by
    rw [hs, ← Set.ncard_eq_toFinset_card A hfin]; exact hcard
  have hR := h a hs0 hs5 ha ⟨c, ρ, fun i => Metric.mem_sphere.mp (hcirc (hr ▸ ⟨i, rfl⟩))⟩
  exact ⟨hfin, hne, toSet ha hr hR⟩

end TargetO.Ramsey

#print axioms TargetO.Ramsey.B_circle
