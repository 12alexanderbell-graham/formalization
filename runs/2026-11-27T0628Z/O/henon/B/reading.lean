import Mathlib

open scoped Laplacian

namespace ReaderB

/-- Theorem 1.1: no positive `u, v ∈ C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)` solve the Hénon–Lane–Emden system
at every `x ≠ 0` under the subcriticality condition. -/
theorem reading_henon_theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q A B : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hsub : (n + A) / (p + 1) + (n + B) / (q + 1) > (n : ℝ) - 2) :
    ¬ ∃ u v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ 2 u {0}ᶜ ∧ ContDiffOn ℝ 2 v {0}ᶜ ∧ Continuous u ∧ Continuous v ∧
      (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
        -(Δ u x) = ‖x‖ ^ A * v x ^ p ∧ -(Δ v x) = ‖x‖ ^ B * u x ^ q) := sorry

/-- Corollary 1.2: unweighted Lane–Emden conjecture. -/
theorem reading_henon_corollary_1_2 (n : ℕ) (hn : 3 ≤ n) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hsub : 1 / (p + 1) + 1 / (q + 1) > ((n : ℝ) - 2) / n) :
    ¬ ∃ u v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 2 u ∧ ContDiff ℝ 2 v ∧ (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), -(Δ u x) = v x ^ p ∧ -(Δ v x) = u x ^ q) := sorry

/-
Ambiguities / choices.
* Laplacian: `Laplacian.laplacian` (notation `Δ`, scoped in `Laplacian`), the instance for
  functions `E → F` on a finite-dimensional real inner product space, here
  `E = EuclideanSpace ℝ (Fin n)`. It is defined from the global second derivative
  `iteratedFDeriv`; at x ≠ 0 it only depends on u near x, where u is C², so it agrees with the
  classical Laplacian. (Not `laplacianWithin`: unnecessary since {0}ᶜ is open.) Its value at 0
  is never used in Theorem 1.1 (equations only for x ≠ 0).
* C²(ℝⁿ∖{0}) ∩ C(ℝⁿ): `ContDiffOn ℝ 2 u {0}ᶜ ∧ Continuous u`. Positivity at all x including 0.
* Functions are real-valued on `EuclideanSpace ℝ (Fin n)`; n is a natural number, hypotheses
  n ≥ 2 (Thm) and n ≥ 3 (Cor) included. Subcriticality inequality has casts to ℝ.
* Powers `‖x‖^A`, `v^p`, `u^q` are `rpow`. Junk-free: at x ≠ 0 the base ‖x‖ > 0, and u, v > 0
  everywhere, so no rpow of negatives or 0^negative occurs. `-Δ u x` is `-(Δ u x)`.
* Corollary: C²(ℝⁿ) is `ContDiff ℝ 2` on the whole space, equations at every x (including 0),
  strictly positive; `(n-2)/n` with n ≥ 3 so no division by zero.
-/

end ReaderB
