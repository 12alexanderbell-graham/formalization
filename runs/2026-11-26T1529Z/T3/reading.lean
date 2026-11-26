import Mathlib

open Matrix BigOperators

/-- `0.5 * ℤ[i]`: real and imaginary parts are integer multiples of 1/2. -/
def HalfGaussian (z : ℂ) : Prop :=
  ∃ m n : ℤ, z = ((m : ℂ) / 2) + ((n : ℂ) / 2) * Complex.I

theorem reading_algorithm :
    ∃ (f g : Fin 48 → (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] ℂ))
      (C : Fin 48 → Matrix (Fin 4) (Fin 4) ℂ),
      ∀ A B : Matrix (Fin 4) (Fin 4) ℂ,
        A * B = ∑ r : Fin 48, (f r A * g r B) • C r := by
  sorry

theorem reading_entries :
    ∃ (a b c : Fin 48 → Fin 4 → Fin 4 → ℂ),
      (∀ r i j, HalfGaussian (a r i j)) ∧
      (∀ r i j, HalfGaussian (b r i j)) ∧
      (∀ r i j, HalfGaussian (c r i j)) ∧
      ∀ A B : Matrix (Fin 4) (Fin 4) ℂ,
        A * B = ∑ r : Fin 48,
          ((∑ i, ∑ j, a r i j * A i j) * (∑ i, ∑ j, b r i j * B i j)) •
            Matrix.of (c r) := by
  sorry

/-
Ambiguities / reading choices:
1. Bilinear vs general: I read "48 multiplications" as a bilinear (tensor-rank) algorithm: each
   product is (linear form of A) * (linear form of B), no products of A-entries with A-entries.
   Non-bilinear/general arithmetic circuits would be a weaker claim; not formalized.
2. Commutativity: scalars are commutative ℂ; the algorithm is not required to work over
   noncommutative rings (so it need not be usable recursively on block matrices). Only
   ℂ-valued entries are treated. The statement does not say whether it is valid in
   non-commutative settings.
3. Field: ℂ-linear forms. The notebook's "0.5*C" could also mean forms over ℝ-structure
   (e.g. using conjugation); I assume plain ℂ-linearity, no complex conjugation.
4. Coefficient set: "0.5·ℤ[i]" read as {(m + n i)/2 : m n ∈ ℤ}. In reading_entries the
   coefficients of both forms and of the output matrices are all constrained (the
   notebook's three factor matrices); the first theorem has no entry constraint.
5. Output coefficient matrices (the third factor) are indexed by (i,j) of the product, with
   the sum scaled by the product of the two form values; any transposition convention of
   the tensor's third factor is absorbed, as C is existentially quantified.
6. Forms in the first theorem are arbitrary ℂ-linear maps (equivalently, 16 coefficients).
-/
