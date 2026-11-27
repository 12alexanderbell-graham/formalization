import Mathlib

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
