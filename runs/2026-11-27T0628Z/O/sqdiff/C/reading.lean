import Mathlib

/-! Reader C, family O6: "A power saving for square-difference-free sets"
(excerpt `introduction_lines1-30.tex`). -/

/-- `[N] = {1,…,N}`. -/
def bracketN (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- `A` is square-difference-free: there are no `a, b ∈ A` and `m ≥ 1` with `a − b = m²`
(the difference is taken in ℤ, so `(A − A) ∩ {m² : m ≥ 1} = ∅`). -/
def SquareDiffFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → (a : ℤ) - (b : ℤ) ≠ (m : ℤ) ^ 2

/-- Theorem 1.1: there are absolute constants `c > 0` and `C < ∞` such that every
square-difference-free `A ⊆ [N]` (for every `N ≥ 1`) satisfies `|A| ≤ C N^{1−c}`.
Real powers: the base `N` is a positive natural cast to ℝ, so no rpow-of-negative junk occurs. -/
theorem reading_power_saving :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ,
      A ⊆ bracketN N → SquareDiffFree A → (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c) := sorry

/-- Theorem 1.1, "Equivalently" sentence: with the same kind of constants, every subset of `[N]`
with more than `C N^{1−c}` elements contains distinct `a, b` whose absolute difference is
`m²` for some positive integer `m`. -/
theorem reading_power_saving_equivalently :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ,
      A ⊆ bracketN N → C * (N : ℝ) ^ (1 - c) < (A.card : ℝ) →
        ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ m : ℕ, 1 ≤ m ∧ |(a : ℤ) - (b : ℤ)| = (m : ℤ) ^ 2 := sorry

/-!
## Ambiguity notes (reader C, O6)

1. "Square-difference-free" is read directionally: `a − b ≠ m²` for all `a, b ∈ A`, `m ≥ 1`. The
   source's `(A−A) ∩ {m²} = ∅` is the same condition, because `m² > 0` forces `a > b` anyway.
2. The difference is taken in ℤ (the source says "differences in the integers"), so there is no
   ℕ subtraction.
3. `[N]` is `Finset.Icc 1 N`, and `N ≥ 1` is assumed in the theorem (the source says "every integer
   N ≥ 1").
4. The constants are read as `∃ c, 0 < c ∧ ∃ C, ∀ N ...` (the same `c, C` for all `N` and `A`).
   The source says "absolute constants `c > 0` and `C < ∞`", which I read as a real `C` (the `< ∞`
   is automatic for reals).
5. Caveat: `c` is not restricted to `c ≤ 1`, and none is stated in the source. For `c > 1` the
   bound `C N^{1−c}` tends to 0, but `A = {1}` is square-difference-free with `|A| = 1`, so the
   literal statement would be false for `c > 1`. The theorem therefore only holds for `c ∈ (0, 1]`.
   The statement as written is still formalized literally; the exponent constraint is noted here.
6. The "Equivalently" sentence: I read "every subset of [N] larger than C N^{1−c}" as
   `C N^{1−c} < |A|`, and "distinct elements whose absolute difference is the square of a positive
   integer" as `a ≠ b` with `|a − b| = m²`, `m ≥ 1`. In my form the constants are existentially
   quantified again (the second theorem is its own `∃ c, ∃ C`), so the two theorems are not linked
   by a shared witness. The source's "equivalently" implies a shared witness; I did not encode that
   link as a single statement.
7. The source's `s(N)` (the max size) is defined in the excerpt but not used in Theorem 1.1, so it is
   not encoded (the theorem is stated for every `A`, which is equivalent to the bound on `s(N)`).
-/
