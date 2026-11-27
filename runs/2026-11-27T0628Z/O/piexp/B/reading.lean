import Mathlib

open Real

namespace ReadingO9B

/-- Irrationality exponent μ(x) = sup {ν > 0 : 0 < |x - p/q| < q^(-ν) for infinitely many
coprime p, q ∈ ℤ, q ≥ 2}, as an `EReal` sSup (empty -> ⊥, unbounded -> ⊤; no junk). -/
noncomputable def mu (x : ℝ) : EReal :=
  sSup {e : EReal | ∃ ν : ℝ, 0 < ν ∧ e = (ν : EReal) ∧
    {pq : ℤ × ℤ | 2 ≤ pq.2 ∧ Int.gcd pq.1 pq.2 = 1 ∧
      0 < |x - (pq.1 : ℝ) / pq.2| ∧ |x - (pq.1 : ℝ) / pq.2| < ((pq.2 : ℝ)) ^ (-ν)}.Infinite}

/-- Theorem 1.1, first sentence: μ(π) = 2. -/
theorem reading_thm_1_1_mu : mu π = 2 := sorry

/-- Theorem 1.1, "more precisely": for every ν > 2 there is an integer Q with
|π - p/q| ≥ q^(-ν) for all integers p and all q ≥ Q. -/
theorem reading_thm_1_1_precise (ν : ℝ) (hν : 2 < ν) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q → ((q : ℝ)) ^ (-ν) ≤ |π - (p : ℝ) / q| := sorry

/-- Corollary (abstract): the Flint–Hills series Σ_{n≥1} 1/(n³ sin² n) converges
(terms are nonnegative, so convergence = summability; indexed by n+1 to start at 1). -/
theorem reading_flint_hills :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3 * (Real.sin ((n + 1 : ℕ) : ℝ)) ^ 2)) := sorry

end ReadingO9B

/-
Ambiguities / choices (reader B):
* μ is defined for every real x, as in the source formula (stated there for irrational x). Sup taken in
  EReal to avoid sSup junk of empty/unbounded ℝ-sets. Coprime: Int.gcd p q = 1. "Infinitely many
  coprime p,q" -> infinitely many pairs (p,q) ∈ ℤ×ℤ. q ≥ 2 so base of rpow is positive.
* "Integer Q(ν)" in the more-precise inequality: source allows any integer, which would make q^(-ν)
  an rpow of a negative for q ≤ 0 (junk). I add 2 ≤ Q; equivalent in strength (replace Q by max Q 2)
  and avoids negative bases. Reduced or not fractions both covered (all p).
* Second statement is non-effective in Q (as source remarks); ∃ Q matches.
* Flint–Hills: sin of the real number n (radians); sin n ≠ 0 since π irrational, so no division-by-zero
  junk in terms (n ≥ 1). Shifted index n+1 avoids the n=0 junk term.
* Proved in source: Thm 1.1 (main result); μ(π)=2 follows from it plus the pigeonhole lower bound
  μ ≥ 2 (stated in source as known). The Flint–Hills convergence is stated as a consequence/corollary
  (via Alekseyev: convergence requires μ(π) ≤ 5/2, and presumably sufficiency of μ(π)<... ; the excerpt
  cuts off, so I can't tell whether the source proves or cites the implication).
-/
