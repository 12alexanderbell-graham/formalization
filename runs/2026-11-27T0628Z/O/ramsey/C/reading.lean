import Mathlib

open Set TensorProduct

noncomputable section

namespace ReaderC

/-- Euclidean space of dimension d. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A finite nonempty set A in a Euclidean space is Ramsey if, for every r ≥ 2, there is D ≥ 1
such that every colouring c : ℝ^D → {1,…,r} (arbitrary function) is constant on a congruent copy
of A, i.e. on f(A) for some map f : A → ℝ^D preserving every pairwise distance. -/
def IsRamsey {d : ℕ} (A : Set (E d)) : Prop :=
  A.Finite ∧ A.Nonempty ∧
    ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
      ∀ c : E D → Fin r, ∃ f : E d → E D,
        (∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y) ∧
        ∃ k : Fin r, ∀ x ∈ A, c (f x) = k

/-- A is subtransitive: A is isometric to a subset T of a finite set S (in some Euclidean space)
whose own isometry group acts transitively on S. -/
def IsSubtransitive {d : ℕ} (A : Set (E d)) : Prop :=
  ∃ (e : ℕ) (S : Set (E e)), S.Finite ∧ S.Nonempty ∧
    (∀ x : S, ∀ y : S, ∃ g : S ≃ S,
        (∀ u v : S, dist (g u : E e) (g v : E e) = dist (u : E e) (v : E e)) ∧ g x = y) ∧
    ∃ T : Set (E e), T ⊆ S ∧
      ∃ f : E d → E e, Set.BijOn f A T ∧
        ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y

/-- A set lies on a circle: there are a centre c, orthonormal u, v spanning the plane of the circle,
and R > 0 with every point of A equal to c + R (cos θ · u + sin θ · v) for some θ. -/
def OnCircle {d : ℕ} (A : Set (E d)) : Prop :=
  ∃ (c u v : E d) (R : ℝ), 0 < R ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
    ∀ x ∈ A, ∃ θ : ℝ, x = c + R • (Real.cos θ • u + Real.sin θ • v)

/-- The subfield of ℝ generated over ℚ by the coordinates a_i,α of the points. -/
def coordField {s d : ℕ} (a : Fin s → E d) : Subfield ℝ :=
  Subfield.closure (Set.range fun p : Fin s × Fin d => a p.1 p.2)

/-- p_i = (1, a_i) as a vector indexed by 0,…,d, with entries in the coordinate field. -/
def coordPt {s d : ℕ} (a : Fin s → E d) (i : Fin s) : Fin (d + 1) → coordField a :=
  Fin.cases (motive := fun _ => coordField a) 1
    (fun α : Fin d => ⟨a i α, Subfield.subset_closure ⟨(i, α), rfl⟩⟩)

/-- B = F ⊗_ℚ F. -/
abbrev TB {s d : ℕ} (a : Fin s → E d) := coordField a ⊗[ℚ] coordField a

/-- The multiplication map m_F : F ⊗_ℚ F → F, x ⊗ y ↦ x y. -/
def mF {s d : ℕ} (a : Fin s → E d) : TB a →ₐ[ℚ] coordField a :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ (coordField a)) (AlgHom.id ℚ (coordField a))
    (fun _ _ => Commute.all _ _)

/-- The existence of the matrix P in the classification: the tensor evaluation identities
(p_i ⊗ 1)^T P (1 ⊗ p_i) = 0 hold in B before multiplication, and m_F(P_αβ) = δ_αβ for
1 ≤ α, β ≤ d (indices of the (d+1)×(d+1) matrix are 0,…,d; the spatial block is `succ`). -/
def ClassificationWitness {s d : ℕ} (a : Fin s → E d) : Prop :=
  ∃ P : Matrix (Fin (d + 1)) (Fin (d + 1)) (TB a),
    (∀ i : Fin s,
        ∑ α : Fin (d + 1), ∑ β : Fin (d + 1),
          (coordPt a i α ⊗ₜ[ℚ] (1 : coordField a)) * P α β *
            ((1 : coordField a) ⊗ₜ[ℚ] coordPt a i β) = 0) ∧
    (∀ α β : Fin d, mF a (P α.succ β.succ) = if α = β then 1 else 0)

/-- Classification theorem: for a finite set A = {a_1,…,a_s} ⊂ ℝ^d, s ≥ 2, with affine span ℝ^d,
A is Ramsey iff the tensor criterion holds. -/
theorem readingC_classification {s d : ℕ} (a : Fin s → E d) (ha : Function.Injective a)
    (hs : 2 ≤ s) (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    IsRamsey (Set.range a) ↔ ClassificationWitness a :=
  sorry

/-- Consequence (i): every subtransitive set (nonempty, see comment) is Ramsey. -/
theorem readingC_subtransitive_ramsey {d : ℕ} (A : Set (E d)) (hne : A.Nonempty)
    (hA : IsSubtransitive A) : IsRamsey A :=
  sorry

/-- Consequence (ii): every nonempty set of at most five points on a circle is Ramsey. -/
theorem readingC_five_points_on_circle_ramsey {d : ℕ} (A : Set (E d)) (hne : A.Nonempty)
    (hcard : A.encard ≤ 5) (hcirc : OnCircle A) : IsRamsey A :=
  sorry

/-- Consequence (iii), the classical necessity (Erdős–Graham–Montgomery–Rothschild–Spencer–Straus):
every finite Ramsey set is spherical, i.e. lies on a sphere of ℝ^d. -/
theorem readingC_ramsey_is_spherical {d : ℕ} (A : Set (E d)) (hA : IsRamsey A) :
    ∃ (c : E d) (R : ℝ), ∀ x ∈ A, dist x c = R :=
  sorry

end ReaderC

end

/-
Ambiguities and choices (reader C):
* Ramsey: "Euclidean space" is taken to be ℝ^d with A ⊂ ℝ^d (the ambient dimension d of A is
  fixed; the colouring space ℝ^D is over all D ≥ 1 as the definition requires). "Finite nonempty"
  is part of `IsRamsey` (`A.Finite ∧ A.Nonempty`), as in the first paragraph.
* "Congruent copy": f : A → ℝ^D (extended to the ambient ℝ^d as a function) preserving every
  pairwise distance exactly (original scale); the copy is f(A). Colourings are arbitrary functions
  `E D → Fin r` (no measurability). Congruence need not be realised by a global isometry.
* Subtransitive: "isometry group of S" is read intrinsically, as self-bijections g : S ≃ S preserving
  distances within S, transitive on S; "isometric copy of a subset" = A is in distance-preserving
  bijection with some T ⊆ S (`Set.BijOn f A T` with f distance-preserving on A). Hence `A.Nonempty`
  is added as a hypothesis in consequence (i) (subtransitive sets with T = ∅ are excluded; the
  empty set is not Ramsey by definition). Finiteness of A follows from the BijOn with finite T and
  is not separately assumed.
* Classification: the tensor product is `TB a := F ⊗[ℚ] F` with F = `coordField a`, the subfield of
  ℝ generated over ℚ by all coordinates a_i,α (this is the exact field Q((a_i)_α) in the source).
  The ambient point set is `Set.range a` with `a` injective and s ≥ 2; the affine-span condition is
  `affineSpan ℝ (Set.range a) = ⊤`. p_i ⊗ 1 and 1 ⊗ p_i are formed componentwise. The row/column
  index 0 is the constant coordinate (`Fin.cases`), and the spatial block uses `Fin.succ`
  (indices 1..d). m_F is `Algebra.TensorProduct.lift` of identities. The field F is an ℚ-algebra
  via Mathlib's `DivisionRing` instance. The statement is independent of representative as the
  source says; no proof of that is included here.
* Circle: "points on a circle" is read as lying on a circle of a 2-plane c + span{u, v} with u, v
  orthonormal and radius R > 0 (in ℝ^d, d ≥ 2 in practice; the definition does not force it).
* Spherical: a sphere in ℝ^d, i.e. a centre and radius with all points at that distance.
* Rounding: the excerpt cuts off mid-sentence at line 116, so the source's exact wording of
  consequence (i) (that subtransitive sets are Ramsey) is inferred from the abstract framing
  "Ramsey exactly when it embeds in a finite transitive set" and the sentence "every subtransitive
  set satisfies the tensor condition". This is recorded as a reading, not verified.
-/
