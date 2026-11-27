import Mathlib

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
