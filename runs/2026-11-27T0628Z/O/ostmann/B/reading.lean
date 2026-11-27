import Mathlib

/-- The set of positive primes inside ℕ₀ (= ℕ). -/
def primeSet : Set ℕ := {p | p.Prime}

/-- Sumset `A + B = {a + b}`. -/
def sumset (A B : Set ℕ) : Set ℕ := {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- Theorem 1.1 (Ostmann's conjecture). -/
theorem reading_ostmann (A B : Set ℕ) (hA : 2 ≤ A.encard) (hB : 2 ≤ B.encard) :
    (symmDiff (sumset A B) primeSet).Infinite := sorry

/-- "Equivalently": every finite modification of the primes is not a sumset of two sets
with at least two elements each. -/
theorem reading_ostmann_equiv (P : Set ℕ) (hP : (symmDiff P primeSet).Finite)
    (A B : Set ℕ) (hA : 2 ≤ A.encard) (hB : 2 ≤ B.encard) :
    sumset A B ≠ P := sorry

/- Ambiguities / choices:
* ℕ₀ is Lean ℕ; primes are Nat.Prime (positive by definition). Sets A,B arbitrary (possibly
  infinite), so "|A| ≥ 2" is 2 ≤ encard (ℕ∞), no junk.
* Theorem 2.x ("two infinite summands") is not in my excerpt (only lines 1-21), so omitted.
* "Asymptotically equal" = finite symmetric difference; the "Equivalently" sentence is
  stated as the second theorem with sumset A B = P exactly (a finite modification P of primes
  is not equal to A+B). Equivalence with the first: A+B = P gives finite symmdiff... the
  second follows from the first by triangle on symmetric differences; formalized separately.
-/
