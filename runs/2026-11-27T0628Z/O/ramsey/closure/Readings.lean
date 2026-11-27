import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

open TensorProduct

/-- `ℝ^m` with its Euclidean distance. -/
abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- A finite nonempty set `A ⊂ ℝ^m` is Ramsey if for every integer `r ≥ 2` there is an
integer `D ≥ 1` such that every map `c : ℝ^D → {1,…,r}` is constant on a congruent copy of
`A`. A congruent copy is the image of `A` under a map preserving every pairwise distance. -/
def IsRamsey {m : ℕ} (A : Set (E m)) : Prop :=
  A.Finite ∧ A.Nonempty ∧
    ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
      ∀ c : E D → Fin r, ∃ f : E m → E D,
        (∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y) ∧
        ∃ col : Fin r, ∀ x ∈ A, c (f x) = col

/-- The coordinate field `F = ℚ((a_i)_α)` ⊂ ℝ. -/
noncomputable def coordField {d s : ℕ} (a : Fin s → E d) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ {x : ℝ | ∃ i α, a i α = x}

/-- The coordinate `(a_i)_α` as an element of `F`. -/
noncomputable def coordInF {d s : ℕ} (a : Fin s → E d) (i : Fin s) (α : Fin d) : coordField a :=
  ⟨a i α, IntermediateField.subset_adjoin ℚ _ ⟨i, α, rfl⟩⟩

/-- `p_i = (1, a_i) ∈ F^{d+1}`, index `0` being the constant coordinate. -/
noncomputable def liftPt {d s : ℕ} (a : Fin s → E d) (i : Fin s) : Fin (d + 1) → coordField a :=
  Fin.cons 1 (coordInF a i)

/-- Classification theorem. `B = F ⊗_ℚ F`, `m_F = Algebra.TensorProduct.lmul' ℚ`. -/
theorem reading_classification (d s : ℕ) (a : Fin s → E d) (hinj : Function.Injective a)
    (hs : 2 ≤ s) (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    IsRamsey (Set.range a) ↔
      ∃ P : Matrix (Fin (d + 1)) (Fin (d + 1)) (coordField a ⊗[ℚ] coordField a),
        (∀ i : Fin s,
          ∑ α : Fin (d + 1), ∑ β : Fin (d + 1),
            (liftPt a i α ⊗ₜ[ℚ] (1 : coordField a)) * P α β *
              ((1 : coordField a) ⊗ₜ[ℚ] liftPt a i β) = 0) ∧
        (∀ α β : Fin d,
          Algebra.TensorProduct.lmul' ℚ (P α.succ β.succ) = if α = β then 1 else 0) :=
  sorry

/-- A finite set `T ⊂ ℝ^k` is transitive if its isometries (distance-preserving self-maps of
`T`) act transitively on its points. -/
def IsTransitiveSet {k : ℕ} (T : Set (E k)) : Prop :=
  T.Finite ∧ ∀ x ∈ T, ∀ y ∈ T, ∃ g : E k → E k,
    (∀ u ∈ T, g u ∈ T) ∧ (∀ u ∈ T, ∀ v ∈ T, dist (g u) (g v) = dist u v) ∧ g x = y

/-- `A` is subtransitive: an isometric copy of a subset of a finite transitive set. -/
def IsSubtransitive {m : ℕ} (A : Set (E m)) : Prop :=
  ∃ k : ℕ, ∃ T : Set (E k), IsTransitiveSet T ∧ ∃ f : E m → E k,
    (∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y) ∧ f '' A ⊆ T

/-- Consequence (i): every (nonempty) subtransitive set is Ramsey. -/
theorem reading_subtransitive_ramsey (m : ℕ) (A : Set (E m)) (hne : A.Nonempty)
    (hA : IsSubtransitive A) : IsRamsey A :=
  sorry

/-- `A` lies on a circle: there is a 2-dimensional affine plane `Pl`, a centre `c ∈ Pl` and a
radius `ρ > 0` with `A ⊆ {x ∈ Pl | dist x c = ρ}`. -/
def OnCircle {m : ℕ} (A : Set (E m)) : Prop :=
  ∃ Pl : AffineSubspace ℝ (E m), Module.finrank ℝ Pl.direction = 2 ∧
    ∃ c ∈ Pl, ∃ ρ : ℝ, 0 < ρ ∧ A ⊆ {x | x ∈ Pl ∧ dist x c = ρ}

/-- Consequence (ii): every nonempty set of at most five points on a circle is Ramsey. -/
theorem reading_circle_five_ramsey (m : ℕ) (A : Finset (E m)) (hne : A.Nonempty)
    (hcard : A.card ≤ 5) (hcirc : OnCircle (A : Set (E m))) : IsRamsey (A : Set (E m)) :=
  sorry

/-- `A` is spherical: it lies on some sphere. -/
def IsSpherical {m : ℕ} (A : Set (E m)) : Prop :=
  ∃ c : E m, ∃ ρ : ℝ, A ⊆ Metric.sphere c ρ

/-- Consequence (iii) (Erdős–Graham–Montgomery–Rothschild–Spencer–Straus):
every finite Ramsey set is spherical. -/
theorem reading_ramsey_spherical (m : ℕ) (A : Set (E m)) (hA : IsRamsey A) :
    IsSpherical A :=
  sorry

end ReaderA

/-
Ambiguities and choices (reader A):

1. "A finite nonempty set in a Euclidean space": taken as `A ⊆ ℝ^m = EuclideanSpace ℝ (Fin m)`
   for some `m`; finiteness and nonemptiness are part of `IsRamsey`.
2. "Congruent copy of A in ℝ^D": the image `f '' A` of a map `f : ℝ^m → ℝ^D` preserving all
   pairwise distances on `A` (at the original scale). Such `f` is injective on `A`, so this is
   exactly a distance-preserving bijection of `A` onto a subset of `ℝ^D`. `f` is only required
   to preserve distances on `A`; its values off `A` are irrelevant.
3. Colors `{1,…,r}` encoded as `Fin r`; colorings are arbitrary functions (no measurability).
   `D ≥ 1` kept as stated. `D` may depend on `r` (quantifier order ∀ r ∃ D ∀ c as in source).
4. Classification: no change of substance was needed. `A = {a_1,…,a_s}` is encoded as an
   injective family `a : Fin s → ℝ^d` ("the points are distinct"), `s ≥ 2`, affine span `= ⊤`.
   `F` is the intermediate field `ℚ((a_i)_α) ⊆ ℝ` (`IntermediateField.adjoin`), `B` is
   `F ⊗[ℚ] F`, and `m_F` is `Algebra.TensorProduct.lmul' ℚ : F ⊗ F →ₐ[ℚ] F` (x ⊗ y ↦ xy).
   `p_i = (1, a_i)` via `Fin.cons` with index `0` the constant coordinate; spatial indices
   `1 ≤ α ≤ d` are `α.succ` for `α : Fin d`.
   The bilinear expression `(p_i ⊗ 1)ᵀ P (1 ⊗ p_i)` is written out as the double sum
   `∑_{α,β} (p_iα ⊗ 1) · P_{αβ} · (1 ⊗ p_iβ)` in the commutative ring `B` (componentwise
   formation of `p_i ⊗ 1`, `1 ⊗ p_i`). No condition on row/column `0` of `P` in the second
   clause, as stated. `δ_{αβ}` is `if α = β then 1 else 0` in `F`.
   The Ramsey side is `IsRamsey (Set.range a)` for the set itself (not "up to congruence");
   the theorem is stated for the chosen representative, as in the source.
5. Subtransitive: "isometric copy of a subset of a finite transitive set". Transitive set
   `T ⊆ ℝ^k` (some `k`): finite, and for all `x, y ∈ T` there is a self-map `g` of `T`
   preserving distances on `T` with `g x = y`. (A distance-preserving self-map of a finite
   set is a bijection; and every such map extends to an isometry of `ℝ^k`, so this agrees
   with "isometries of the finite set".) `A` is subtransitive if a distance-preserving
   `f : ℝ^m → ℝ^k` (on `A`) maps `A` into such a `T`. Consequence (i) adds `A.Nonempty`,
   since the Ramsey definition requires nonempty sets (the empty set is trivially
   subtransitive). Finiteness of `A` follows from the injection into `T`.
6. Circle in `ℝ^m`: points of a 2-dimensional affine plane at a fixed positive distance
   `ρ > 0` from a centre in that plane (degenerate radius-0 "circles" excluded). Stated for
   general `m` rather than only `ℝ²`. "At most five points" uses a `Finset` with `card ≤ 5`
   (avoiding `Set.ncard`, which is junk `0` on infinite sets).
7. Spherical: `A ⊆ Metric.sphere c ρ` for some `c ∈ ℝ^m`, `ρ ∈ ℝ` (no positivity on `ρ`,
   so a singleton in `ℝ⁰` counts as spherical, consistent with singletons being Ramsey).
   "Finite" is already included in `IsRamsey`.
-/

-- ===== reader B =====

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

-- ===== reader C =====

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
