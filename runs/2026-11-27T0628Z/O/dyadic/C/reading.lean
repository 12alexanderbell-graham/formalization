import Mathlib

open MeasureTheory Set

namespace ReadingC

/-- D = {2^{-n} : n ∈ ℕ, n ≥ 1}. -/
def dyD : Set ℝ :=
  {d | ∃ n : ℕ, 1 ≤ n ∧ d = (2 : ℝ) ^ (-(n : ℤ))}

/-- The nontrivial affine copy x + sD = {x + s d : d ∈ D}. -/
def dyAffineCopy (x s : ℝ) : Set ℝ :=
  (fun d : ℝ => x + s * d) '' dyD

/-- Theorem 1.1 (both forms, sharing the same E_η): for every η ∈ (0,1) there is a compact
E_η ⊆ [0,1] with m(E_η) > 1 - η such that
  (i) for every x ∈ ℝ and s ∈ ℝ \ {0}, x + sD ⊄ E_η;
  (ii) (Equivalently) for every such x, s there is n ≥ 1 with x + s 2^{-n} ∉ E_η. -/
theorem reading_dyadic_main :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      IsCompact E ∧ E ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (1 - η) < volume E ∧
      (∀ x s : ℝ, s ≠ 0 → ¬ (dyAffineCopy x s ⊆ E)) ∧
      (∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * (2 : ℝ) ^ (-(n : ℤ)) ∉ E) := sorry

end ReadingC

/-
Ambiguities and choices (reader C):

1. D = {2^{-n} : n ∈ ℕ, n ≥ 1} written as a Set ℝ with existential over n : ℕ and 1 ≤ n;
   the power is the ℤ-power 2^(-(n:ℤ)) (zpow), so 2^{-n} is exactly the source's expression.

2. x + sD is the image of D under d ↦ x + s d (as a set, so no multiplicity issues).
   "Nontrivial affine copy" with s ≠ 0 is the hypothesis s ≠ 0 on each universal statement.

3. "x + sD ⊄ E_η" is ¬ (dyAffineCopy x s ⊆ E). Read as: not a subset, i.e. some point of
   x + sD lies outside E_η. Equivalent to clause (ii) by unfolding the image; I kept both.

4. m(E_η) > 1 - η: "m" is Lebesgue measure, so volume on ℝ (MeasureTheory.volume). Measures
   are ENNReal, so the comparison is ENNReal.ofReal (1 - η) < volume E. Since η < 1 we have
   1 - η > 0, so ofReal does not clip the bound (no junk value here).

5. "compact set E_η ⊆ [0,1]": IsCompact E and E ⊆ Icc 0 1.

6. Quantifier scope: E is chosen after η (the source says "for every η there is E_η").
   The η ∈ (0,1) restriction is stated as 0 < η and η < 1.

7. "for every x ∈ ℝ and every s ∈ ℝ \ {0}" is ∀ x s : ℝ, s ≠ 0 → ...; this is literal.

8. Clause (ii) takes n : ℕ with 1 ≤ n, matching n ∈ ℕ, n ≥ 1 in D's definition. The
   source writes "integer n ≥ 1", so ℕ with 1 ≤ n is the literal reading.

9. I bundled both forms into one theorem with a shared E, since the source states one
   theorem about one E_η. The brief asked for both forms as the theorem's content.
-/
