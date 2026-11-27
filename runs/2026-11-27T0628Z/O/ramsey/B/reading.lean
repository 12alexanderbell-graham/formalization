import Mathlib

namespace ReaderB

open scoped TensorProduct

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A finite nonempty A ⊆ R^d is Ramsey: for every r ≥ 2 there is D ≥ 1 such that every colouring
c : R^D → {1..r} (here Fin r) is constant on a congruent copy of A (a distance-preserving map on A). -/
def IsRamsey {d : ℕ} (A : Set (E d)) : Prop :=
  A.Finite ∧ A.Nonempty ∧
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧ ∀ c : E D → Fin r,
    ∃ f : E d → E D, (∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y) ∧
      ∃ i : Fin r, ∀ x ∈ A, c (f x) = i

/-- Subtransitive: isometric to a subset of a finite subset T of some Euclidean space whose
isometry group acts transitively. -/
def IsSubtransitive {d : ℕ} (A : Set (E d)) : Prop :=
  ∃ (e : ℕ) (T : Set (E e)), T.Finite ∧ (∀ x y : T, ∃ g : T ≃ᵢ T, g x = y) ∧
    ∃ f : E d → E e, (∀ x ∈ A, f x ∈ T) ∧ ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y

/-- Spherical: lies on a sphere (centre c, radius ρ). -/
def IsSpherical {d : ℕ} (A : Set (E d)) : Prop :=
  ∃ (c : E d) (ρ : ℝ), ∀ x ∈ A, dist x c = ρ

section Tensor

variable {s d : ℕ} (a : Fin s → E d)

/-- F = ℚ(all coordinates of all a_i), as a subfield of ℝ. -/
noncomputable def coordField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (Set.range fun p : Fin s × Fin d => a p.1 p.2)

/-- p_i = (1, a_i) ∈ F^(d+1), index 0 the constant coordinate. -/
noncomputable def pvec (i : Fin s) : Fin (d + 1) → coordField a :=
  Fin.cons 1 fun α => ⟨a i α, IntermediateField.subset_adjoin ℚ _ ⟨(i, α), rfl⟩⟩

/-- m_F : F ⊗ F → F, x ⊗ y ↦ x y. -/
noncomputable def mF : (coordField a ⊗[ℚ] coordField a) →ₐ[ℚ] coordField a :=
  Algebra.TensorProduct.lmul' ℚ

/-- Existence of the tensor matrix P ∈ Mat_{d+1}(B), B = F ⊗_ℚ F. -/
def HasTensorMatrix : Prop :=
  ∃ P : Matrix (Fin (d + 1)) (Fin (d + 1)) (coordField a ⊗[ℚ] coordField a),
    (∀ i : Fin s, ∑ α, ∑ β,
        ((pvec a i α) ⊗ₜ[ℚ] (1 : coordField a)) * P α β * ((1 : coordField a) ⊗ₜ[ℚ] (pvec a i β)) = 0) ∧
    ∀ α β : Fin d, mF a (P α.succ β.succ) = if α = β then 1 else 0

end Tensor

/-- Classification theorem. A = {a_1..a_s} ⊆ R^d, distinct points, s ≥ 2, affine span everything. -/
theorem readingClassification {s d : ℕ} (a : Fin s → E d) (hinj : Function.Injective a)
    (hs : 2 ≤ s) (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    IsRamsey (Set.range a) ↔ HasTensorMatrix a := sorry

/-- (i) Every subtransitive set is Ramsey. -/
theorem readingSubtransitive {d : ℕ} (A : Set (E d)) (hne : A.Nonempty) (h : IsSubtransitive A) :
    IsRamsey A := sorry

/-- (ii) Every nonempty set of at most five points on a circle in the plane is Ramsey. -/
theorem readingCircleFive (A : Set (E 2)) (hne : A.Nonempty) (hfin : A.Finite) (hcard : A.ncard ≤ 5)
    (c : E 2) (ρ : ℝ) (hcirc : A ⊆ Metric.sphere c ρ) : IsRamsey A := sorry

/-- (iii) Every finite Ramsey set is spherical. -/
theorem readingRamseySpherical {d : ℕ} (A : Set (E d)) (h : IsRamsey A) : IsSpherical A := sorry

end ReaderB

/-
Ambiguities / choices.
* Euclidean space is EuclideanSpace ℝ (Fin d). A set A ⊆ R^d is Ramsey (IsRamsey) when finite, nonempty and
  for all r ≥ 2 there is D ≥ 1 with: every c : R^D → Fin r (arbitrary function, colours {1..r} as Fin r,
  which is r-element so no wrap-around issue) has f : R^d → R^D preserving all pairwise distances on A
  with c ∘ f constant on A. "Congruent copy" = image of A under a distance-preserving map on A (f only matters on A).
  Ramsey is not required to be defined for A in all R^d with the same d; ambient dimension is part of the type, but
  the notion is intrinsic (any such copy).
* Classification: points given as an injective enumeration a : Fin s → R^d, s ≥ 2, affine span ⊤ (so d ≥ 1 is implied).
  F = IntermediateField.adjoin ℚ (coordinates) ⊆ ℝ, B = F ⊗[ℚ] F, mF = Algebra.TensorProduct.lmul'.
  Indices 0..d of p_i and P are Fin (d+1) with Fin.cons putting the constant 1 at index 0; the spatial condition uses
  α.succ, β.succ for α,β : Fin d (no ℕ arithmetic). The evaluation equation (p_i⊗1)^T P (1⊗p_i) = 0 is written out as the
  double sum over all (d+1)^2 entries with no condition on the constant row/column. Δ is `if α = β then 1 else 0`.
  Nothing changed relative to the source except that the points are enumerated and A is Set.range a.
* (i) subtransitive: ∃ finite T ⊆ R^e whose self-isometry group (T ≃ᵢ T as a metric subtype) acts transitively, and a map f
  on A into T preserving distances (isometric copy). Added hypothesis A.Nonempty (the Ramsey definition needs nonempty;
  finiteness follows from T finite and injectivity of the distance-preserving f).
* (ii) circle: A ⊆ Metric.sphere c ρ in R^2, any ρ (ρ<0 forces empty, ρ=0 singleton; both fine/excluded), finite, nonempty, ncard ≤ 5.
  `Set.ncard` of a finite set is the true cardinality (finiteness assumed explicitly).
* (iii) spherical: ∃ c ρ with all points at distance ρ from c in the same R^d (same as sphere in the affine span, since a sphere
  in R^d meets the span in a sphere). Hypothesis is IsRamsey, which already includes finite and nonempty.
-/
