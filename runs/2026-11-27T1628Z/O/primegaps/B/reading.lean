import Mathlib

namespace ReaderB

open Filter Classical

/-- `p` is the increasing enumeration `p 1 < p 2 < ...` of the primes (index 0 unused). -/
def IsPrimeEnum (p : ℕ → ℕ) : Prop :=
  (∀ n, 1 ≤ n → (p n).Prime) ∧ (∀ m n, 1 ≤ m → m < n → p m < p n) ∧
    ∀ q, q.Prime → ∃ n, 1 ≤ n ∧ p n = q

/-- Lower asymptotic density `liminf |A ∩ [1,N]| / N`. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop

/-- Theorem 1.1. -/
theorem readingTheorem11 (p : ℕ → ℕ) (hp : IsPrimeEnum p) :
    ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((Finset.Icc 1 N).filter
        (fun n => ((p (n + 1) : ℝ) - p n) > C * Real.log (p n))).card : ℝ) := sorry

/-- Corollary 1.2. -/
theorem readingCorollary12 (p : ℕ → ℕ) (hp : IsPrimeEnum p) :
    0 < lowerDensity {n : ℕ | 1 ≤ n ∧ (p n : ℝ) / n < (p (n + 1) : ℝ) / (n + 1)} := sorry

end ReaderB

/-
Ambiguities and choices.
* p_n: Nat.nth avoided. Instead every theorem is universally quantified over an arbitrary p : ℕ → ℕ
  satisfying IsPrimeEnum (primes at indices >= 1, strictly increasing, hitting every prime). Such p exists
  and is unique on indices >= 1 (p 0 is a free junk value, never used: n >= 1 everywhere), so this is
  equivalent to using the true p_n, with no junk.
* Real subtraction p_{n+1} - p_n is done in ℝ (casts first), so no ℕ truncation. log of p n >= 2, no junk.
* Theorem 1.1: N is a natural number, c real; N0 is ℕ (the text's N0(C) could be real; equivalent).
* Corollary 1.2: the text's lower density is liminf_{N} |A ∩ [1,N]|/N, written with Filter.liminf in ℝ.
  The sequence is in [0,1] for N >= 1 (value at N = 0 is x/0 = 0 but is irrelevant to a liminf at atTop),
  so liminf is the honest one (bounded; no junk sSup issue). The positivity claim is `0 < lowerDensity A`.
* The set A is {n ≥ 1 : p_n/n < p_{n+1}/(n+1)} with real division (n ≥ 1 so no division by 0;
  the 1 ≤ n conjunct in the set avoids n = 0 only).
* Decidability for filter handled with `open Classical`.
-/
