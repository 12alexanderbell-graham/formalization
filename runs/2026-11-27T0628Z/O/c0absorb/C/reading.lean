import Mathlib

namespace ReaderC

/-! Reading of O34: Theorem 1.1.

Definitions written from the source:
* All Banach spaces are real: `NormedSpace ℝ Z`, complete (`CompleteSpace`) and separable
  (`SeparableSpace`).
* c0 = c0(ℕ) = real sequences tending to zero with the sup norm. We use Mathlib's
  `ZeroAtInftyContinuousMap ℕ ℝ` = `ZeroAtInftyContinuousMap ℕ ℝ`: ℕ carries the discrete topology, so
  continuous maps tending to 0 at infinity are exactly the sequences tending to 0, with the
  sup norm (Mathlib's instance).
* "Linear subspace isomorphic to c0": a closed `Submodule ℝ Z` whose subtype is
  linearly and topologically isomorphic to c0, i.e. `Nonempty (Y ≃L[ℝ] ZeroAtInftyContinuousMap ℕ ℝ)`.
* X ⊕_∞ Y: Mathlib's product `Z × ZeroAtInftyContinuousMap ℕ ℝ`, whose norm is the max norm.
* Bi-Lipschitz equivalence: a surjective map F with constants 0 < c ≤ C < ∞ such that
  c·dist(x,x') ≤ dist(F x, F x') ≤ C·dist(x,x') for all x, x'. (dist is the metric induced
  by the norms, so ‖x - x'‖ = dist x x'.)

Ambiguities and choices:
* "Banach space" is read as a real complete normed space; the existential over Z is
  formulated with explicit instance binders so Z is a genuine real Banach space.
* Isomorphism of c0 with a subspace is a linear homeomorphism (`≃L[ℝ]`), not merely a
  bounded linear bijection; for Banach spaces these are the same (open mapping), so no
  information is lost.
* The theorem's existential asserts there is some Z with all listed properties at once.
-/

/-- Theorem 1.1: there is a separable real Banach space Z with no closed linear subspace
isomorphic to c0 and an onto bi-Lipschitz map Z ⊕_∞ c0 → Z. -/
theorem reading_c0absorb_thm11 :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧
      ¬ (∃ Y : Submodule ℝ Z, IsClosed (Y : Set Z) ∧ Nonempty (Y ≃L[ℝ] ZeroAtInftyContinuousMap ℕ ℝ)) ∧
      ∃ F : Z × ZeroAtInftyContinuousMap ℕ ℝ → Z, Function.Surjective F ∧
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          ∀ x y : Z × ZeroAtInftyContinuousMap ℕ ℝ,
            c * dist x y ≤ dist (F x) (F y) ∧ dist (F x) (F y) ≤ C * dist x y := by
  sorry

end ReaderC
