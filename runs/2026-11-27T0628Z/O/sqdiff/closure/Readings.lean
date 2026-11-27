import Mathlib

namespace ReaderA

/-!
Blind reading A, family O6 (sqdiff): "A power saving for square-difference-free sets".
Source: sqdiff/sources/introduction_lines1-30.tex, Theorem 1.1 (`thm:main`), lines 15-25,
with definitions from lines 4-11.
-/

namespace SqDiffReadingA

/-- Source line 4: `[N] = {1, …, N}`, taken inside `ℤ` since the restriction "concerns differences
in the integers" (line 9). -/
def interval (N : ℕ) : Finset ℤ := Finset.Icc 1 (N : ℤ)

/-- The difference set `A - A = {a - b : a, b ∈ A}` computed in `ℤ`. -/
def diffSet (A : Finset ℤ) : Set ℤ := {d | ∃ a ∈ A, ∃ b ∈ A, d = a - b}

/-- The set of positive squares `{m² : m ∈ ℕ, m ≥ 1}` (as integers). -/
def posSquares : Set ℤ := {d | ∃ m : ℕ, 1 ≤ m ∧ d = (m : ℤ) ^ 2}

/-- Source lines 5-7: `A` is square-difference-free if `(A - A) ∩ {m² : m ∈ ℕ, m ≥ 1} = ∅`. -/
def SquareDifferenceFree (A : Finset ℤ) : Prop :=
  diffSet A ∩ posSquares = ∅

/-- Source lines 10-11 (not needed for the theorem, recorded for completeness):
`s(N) = max {|A| : A ⊆ [N] square-difference-free}`. The maximum is over a finite, nonempty
family (`∅` qualifies), so `Finset.sup` gives the true maximum, no junk. -/
noncomputable def s (N : ℕ) : ℕ :=
  open Classical in
  ((interval N).powerset.filter SquareDifferenceFree).sup Finset.card

/-- Theorem 1.1: there are absolute constants `c > 0` and `C < ∞` such that for every integer
`N ≥ 1` and every square-difference-free `A ⊆ [N]`, `|A| ≤ C N^{1-c}`.
(`C` is a real number, hence finite; `N ≥ 1` so the real power has positive base.) -/
theorem reading_thm_1_1 :
    ∃ c C : ℝ, 0 < c ∧
      ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ, A ⊆ interval N → SquareDifferenceFree A →
        (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c) := sorry

/-- Theorem 1.1, "Equivalently" sentence: every subset of `[N]` larger than `C N^{1-c}` contains
distinct elements whose absolute difference is the square of a positive integer.
Stated with its own existential constants, as an independent theorem. -/
theorem reading_thm_1_1_equivalently :
    ∃ c C : ℝ, 0 < c ∧
      ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ, A ⊆ interval N →
        C * (N : ℝ) ^ (1 - c) < (A.card : ℝ) →
          ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ m : ℕ, 1 ≤ m ∧ |a - b| = (m : ℤ) ^ 2 := sorry

end SqDiffReadingA

/-
AMBIGUITIES AND CHOICES (reader A)

1. Ambient type: A ⊆ [N] is modelled as `A : Finset ℤ` with `A ⊆ Finset.Icc 1 N`. Line 9 says
   "the restriction concerns differences in the integers", so differences are taken in ℤ; this
   avoids truncated ℕ subtraction entirely. (Finset rather than Set: A ⊆ [N] is automatically
   finite, and |A| is then `Finset.card`, no `ncard` junk.)

2. Square-difference-free: transcribed literally as `(A - A) ∩ {m² : m ≥ 1} = ∅` with A - A the
   full difference set in ℤ. Since m ≥ 1, m² > 0, so a = b never matters, and the sign of a - b
   is irrelevant up to swapping a, b (equivalently |a - b| is never a positive square).

3. Quantifier order: "There are absolute constants c > 0 and C < ∞ such that, for every integer
   N ≥ 1 and every ..." — ∃ c C first, then ∀ N, ∀ A. "C < ∞" is rendered by C being a real
   number; no positivity of C is imposed (the source does not impose it; it is forced anyway by
   N = 1, A = {1}). No upper bound c < 1 or c ≤ 1 is imposed (not stated; c ≥ 1 would make the
   claim false for large N, so a witness necessarily has c < 1 — harmless).

4. N^{1-c}: `Real.rpow` with base N ≥ 1 > 0, so no rpow-of-nonpositive junk.

5. "Equivalently ...": stated as a separate theorem, with its own ∃ c C (so it is literally the
   contrapositive form). Read "larger than C N^{1-c}" as strict `C N^{1-c} < |A|`;
   "distinct elements whose absolute difference is the square of a positive integer" as
   ∃ a ≠ b in A, ∃ m ≥ 1, |a - b| = m². The range "N ≥ 1" is carried over from the first sentence
   (the "Equivalently" sentence does not restate it; for N = 0 the statement could fail spuriously
   when 1 - c = 0 is not excluded, so keeping N ≥ 1 matches the intended equivalence).

6. `s(N)` (lines 10-11) is defined but not used in the theorems; the theorem as stated is about
   individual sets, not about s(N). It is junk-free since the family is finite and contains ∅.
-/
end ReaderA

namespace ReaderB

/-- `A ⊆ [N] = {1..N}` has no two elements whose difference is a positive square
(difference 0 is not a square of m ≥ 1, so a = b is allowed). -/
def SqDiffFree (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a ≠ b + m ^ 2

/-- Theorem 1.1, first part. -/
theorem reading_sqdiff_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, SqDiffFree N A →
      (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c) := sorry

/-- "Equivalently": any subset of [N] larger than C N^{1-c} has distinct elements whose
absolute difference is a positive square. -/
theorem reading_sqdiff_equiv :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      C * (N : ℝ) ^ (1 - c) < (A.card : ℝ) →
        ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ m : ℕ, 1 ≤ m ∧ |(a : ℤ) - b| = (m : ℤ) ^ 2 := sorry

/- Ambiguities / choices:
* Differences in ℤ; I avoided ℕ subtraction by writing a = b + m^2 (ordered pair, both
  orders quantified) for freeness, and |(a:ℤ)-b| in the equivalent form.
* Constants c>0, C real (C<∞; C may be nonpositive but then bound only holds for empty A, still
  fine as an existential; the theorem is trivial-free since c can't exceed... c>1 would make
  the exponent negative: not excluded by source, but then the claim is stronger/false for
  A={1}; so truthfulness forces c<1 implicitly; I did not add it).
* N^(1-c) is rpow with positive base N ≥ 1, no junk. "Absolute constants" = independent of N, A.
* The two theorems each carry their own ∃ c C; the source's "equivalently" suggests the same
  constants, which the equivalence (contrapositive, a pure logical restatement) would give.
-/
end ReaderB

namespace ReaderC

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
end ReaderC
