import Mathlib
import Readings.Ramsey
import ComparatorChallenges.EuclideanRamseySpherical

/-! # Target O, family O21 (finite Euclidean Ramsey configurations): closures (run 2026-11-27T0628Z).
Frozen statements taken with `type_of%`, never retyped: `ramsey_cospherical` (an injective Ramsey
enumeration is cospherical), `at_most_five_circle_points_ramsey` (at most five distinct points on a circle
in the plane form a Ramsey enumeration) and `subset_of_finite_transitive_ramsey`. The frozen `Ramsey` is a
property of an enumeration `a : Fin s → ℝ^d` (copies are enumerations `b` with the same pairwise
distances); every reader's is a property of a finite nonempty set (copies are maps distance-preserving on
the set). `toSet`/`ofSet` carry one to the other for an injective enumeration of the set.
(The three challenges cannot be imported together — each redeclares `Congruent` and `Ramsey` — so the
closures are split: this file against `EuclideanRamseySpherical`, `ClosureCircle.lean` against
`EuclideanRamseyCircle`.) Closed here: every reader's necessity (iii) and reader B's five-points-on-a-circle (ii) (B states it in the
plane). Not closed: the Classification theorem (no Lean statement in the release); readers A and C's (ii),
stated for circles in ℝ^m (they need a congruence of the circle into the plane); every reader's (i). -/

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

/-- Necessity, in the readers' set form: a finite set with the set Ramsey property lies on a sphere. -/
theorem spherical_of {d : ℕ} (h : type_of% @OAI.EuclideanRamsey.ramsey_cospherical)
    {A : Set (E d)} (hA : A.Finite) (hR : SetRamsey A) : ∃ c : E d, ∃ ρ : ℝ, ∀ x ∈ A, dist x c = ρ := by
  obtain ⟨s, a, ha, hr, -⟩ := enum hA
  obtain ⟨c, ρ, hc⟩ := h a ha (ofSet hr.le hR)
  exact ⟨c, ρ, fun x hx => hc x (hr ▸ hx)⟩

theorem A_spherical : (type_of% @OAI.EuclideanRamsey.ramsey_cospherical) →
    (type_of% @ReaderA.reading_ramsey_spherical) := by
  intro h m A hA
  obtain ⟨c, ρ, hc⟩ := spherical_of h hA.1 hA.2.2
  exact ⟨c, ρ, fun x hx => Metric.mem_sphere.mpr (hc x hx)⟩

theorem B_spherical : (type_of% @OAI.EuclideanRamsey.ramsey_cospherical) →
    (type_of% @ReaderB.readingRamseySpherical) := by
  intro h d A hA
  exact spherical_of h hA.1 hA.2.2

theorem C_spherical : (type_of% @OAI.EuclideanRamsey.ramsey_cospherical) →
    (type_of% @ReaderC.readingC_ramsey_is_spherical) := by
  intro h d A hA
  exact spherical_of h hA.1 hA.2.2

end TargetO.Ramsey

#print axioms TargetO.Ramsey.A_spherical
#print axioms TargetO.Ramsey.B_spherical
#print axioms TargetO.Ramsey.C_spherical
