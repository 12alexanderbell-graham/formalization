import Mathlib

/-! Reader C, family O5: "The additive indecomposability of the primes" (Ostmann's conjecture,
excerpt `01-introduction_lines1-21.tex`). Subsets of ℕ₀ are `Set ℕ`. -/

/-- The set `𝒫` of positive primes, as a subset of `ℕ₀ = ℕ`. -/
def primeSet : Set ℕ := {p | p.Prime}

/-- The sumset `A + B = {a + b : a ∈ A, b ∈ B}`. -/
def sumset (A B : Set ℕ) : Set ℕ := {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- Theorem 1.1 (Ostmann's conjecture). If `|A|, |B| ≥ 2` then `(A + B) △ 𝒫` is infinite.
`|A| ≥ 2` is `2 ≤ A.encard` (`encard` is `⊤` for infinite sets, so no junk value). -/
theorem reading_ostmann (A B : Set ℕ) (hA : 2 ≤ A.encard) (hB : 2 ≤ B.encard) :
    (symmDiff (sumset A B) primeSet).Infinite := sorry

/-- Theorem 1.1, "Equivalently" sentence: every finite modification `S` of `𝒫` (i.e.
`S △ 𝒫` finite) is not of the form `A + B` with `|A|, |B| ≥ 2`. -/
theorem reading_ostmann_equivalently :
    ∀ S : Set ℕ, (symmDiff S primeSet).Finite →
      ∀ A B : Set ℕ, 2 ≤ A.encard → 2 ≤ B.encard → sumset A B ≠ S := sorry

/-!
## Ambiguity notes (reader C, O5)

1. "Asymptotically equal" is read as "symmetric difference finite". I used Mathlib's `symmDiff`
   on `Set ℕ`.
2. "Two infinite summands" is not in the excerpt. The brief's optional Theorem 2.x is not in
   `01-introduction_lines1-21.tex`, so it is not encoded.
3. `|A| ≥ 2` is read as `2 ≤ A.encard` (cardinality, so infinite sets count as large). The source
   says "at least two elements", which matches this. I did not use `ncard`, because `ncard` is 0 for
   infinite sets, which would silently exclude them.
4. `𝒫` is `Nat.Prime`. Since `Nat.Prime` already excludes 0 and 1, "positive primes" is the same set.
5. The source's "asymptotically additively indecomposable" is not in the displayed claim; I used
   the "Equivalently" sentence as the second theorem. I read "every finite modification of 𝒫 is
   additively indecomposable into two sets with at least two elements each" as: no finite
   modification `S` equals `A + B` with both summands of size ≥ 2. The source's wording "every
   finite modification of 𝒫" is taken as the sets `S` with `S △ 𝒫` finite (including `S = 𝒫`).
6. The sentence "it is not asymptotically equal to A+B" is the same as "(A+B) △ 𝒫 is infinite";
   both are encoded by the first theorem.
7. The source cites Ostmann 1956 and Elsholtz-Harper for the conjecture's history; these are
   cited, not proved, and nothing from them is encoded.
-/
