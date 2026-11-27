import Mathlib

/-!
Blind reading A, family O5 (ostmann): "The additive indecomposability of the primes".
Source: ostmann/sources/01-introduction_lines1-21.tex, Theorem 1.1 (`cor:ostmann`), lines 15-20,
with definitions from lines 3-9.
-/

namespace OstmannReadingA

/-- Source line 4: `ℕ₀ = {0,1,2,…}`. Lean's `ℕ` is exactly this. -/
abbrev N0 := ℕ

/-- Source line 3: `𝒫`, the set of positive primes, as a subset of `ℕ₀`. -/
def P : Set N0 := {p | p.Prime}

/-- Source lines 4-5: for `A, B ⊆ ℕ₀`, `A + B = {a + b : a ∈ A, b ∈ B}`. -/
def sumset (A B : Set N0) : Set N0 := {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- Symmetric difference `S △ T`. -/
def symmDiff' (S T : Set N0) : Set N0 := (S \ T) ∪ (T \ S)

/-- Source lines 5-6: two subsets of `ℕ₀` are asymptotically equal if their symmetric difference
is finite. -/
def AsymptoticallyEqual (S T : Set N0) : Prop := (symmDiff' S T).Finite

/-- Theorem 1.1 (Ostmann's conjecture), first sentence: if `A, B ⊆ ℕ₀` satisfy `|A|, |B| ≥ 2`,
then `(A + B) △ 𝒫` is infinite. Cardinality is `Set.encard` (values in `ℕ∞`), so infinite
summands are allowed and correctly count as having at least two elements. -/
theorem reading_thm_1_1 (A B : Set N0) (hA : 2 ≤ A.encard) (hB : 2 ≤ B.encard) :
    (symmDiff' (sumset A B) P).Infinite := sorry

/-- Theorem 1.1, "Equivalently" sentence: every finite modification `Q` of `𝒫` (a subset of `ℕ₀`
with `Q △ 𝒫` finite) is additively indecomposable into two sets with at least two elements each,
i.e. there are no `A, B ⊆ ℕ₀` with `|A|, |B| ≥ 2` and `A + B = Q`. -/
theorem reading_thm_1_1_equivalently (Q : Set N0) (hQ : (symmDiff' Q P).Finite) :
    ¬ ∃ A B : Set N0, 2 ≤ A.encard ∧ 2 ≤ B.encard ∧ sumset A B = Q := sorry

/-- Lines 7-9 phrasing, for the record (same content as `reading_thm_1_1`): `𝒫` is not
asymptotically equal to `A + B` when both summands contain at least two elements. -/
theorem reading_intro_phrasing (A B : Set N0) (hA : 2 ≤ A.encard) (hB : 2 ≤ B.encard) :
    ¬ AsymptoticallyEqual P (sumset A B) := sorry

end OstmannReadingA

/-
AMBIGUITIES AND CHOICES (reader A)

1. ℕ₀ and 𝒫: ℕ₀ is Lean's `ℕ` (contains 0, as the source stipulates). 𝒫 = "positive primes" is
   `{p : ℕ | p.Prime}`; `Nat.Prime` already excludes 0 and 1, so "positive" is automatic.

2. |A| ≥ 2: A and B may be infinite (nothing in the statement restricts them to finite sets, and
   for the conjecture infinite summands are the essential case). I use `Set.encard` (ℕ∞-valued),
   NOT `Set.ncard`, which would assign the junk value 0 to infinite sets and thereby wrongly
   exclude infinite summands from the hypothesis. `2 ≤ A.encard` ⇔ A has two distinct elements.

3. A + B: written out explicitly as `{a + b | a ∈ A, b ∈ B}` (equal to Mathlib's pointwise `A + B`).
   No subtraction occurs, so no ℕ truncation issue.

4. Symmetric difference: written out as `(S \ T) ∪ (T \ S)` (Mathlib's `symmDiff` on sets).

5. "Equivalently, every finite modification of 𝒫 is additively indecomposable into two sets with at
   least two elements each": I read "finite modification of 𝒫" as a set Q ⊆ ℕ₀ with Q △ 𝒫 finite,
   and "indecomposable into two sets with ≥ 2 elements" as: no A, B ⊆ ℕ₀ with |A|,|B| ≥ 2 and
   A + B = Q (exact equality). The summands are taken in ℕ₀ as in the first sentence. Stated as a
   separate theorem. (The equivalence with the first sentence is immediate: (A+B) △ 𝒫 finite ⇔
   A+B is a finite modification of 𝒫.)

6. "Theorem 2.x (two infinite summands)": NOT present in my excerpt (lines 1-21 end right after
   Theorem 1.1), so I do not state it; I do not guess its content. The source labels Theorem 1.1
   `cor:ostmann`, suggesting it is derived as a corollary of a later main theorem not shown.

7. The intro sentence (lines 7-9, "not asymptotically equal to A+B when both summands contain at
   least two elements") is included as `reading_intro_phrasing`; it is the same claim as
   `reading_thm_1_1` modulo symmetry of △.

8. Attribution: the conjecture is Ostmann's (1956); the source presents Theorem 1.1 as its result
   (a proof of the conjecture). The excerpt contains no proof, only the statement.
-/
