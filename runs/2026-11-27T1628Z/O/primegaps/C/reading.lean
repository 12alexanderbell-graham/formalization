import Mathlib

/-
Blind reading C, target O, family O56 "Positive lower density of large prime gaps".
Source read: abstract and 01-introduction.tex lines 1-53 only.
-/

namespace ReaderC

open Filter

/-- Theorem 1.1 (count bound). For every fixed real C > 0 there are c(C) > 0 and
N₀(C) such that for every N ≥ N₀(C), the number of 1 ≤ n ≤ N with
p_{n+1} - p_n > C log p_n is at least c(C) N. -/
theorem reading_O56_thm1
    (p : ℕ → ℕ)
    (hprime : ∀ n, 1 ≤ n → (p n).Prime)
    (hmono : ∀ m n, 1 ≤ m → m < n → p m < p n)
    (honto : ∀ q, q.Prime → ∃ n, 1 ≤ n ∧ p n = q) :
    ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤
        (((Finset.Icc 1 N).filter
            (fun n => (p (n + 1) : ℝ) - (p n : ℝ) > C * Real.log (p n))).card : ℝ) := by
  sorry

/-- Corollary 1.2. The set {n ≥ 1 : p_n / n < p_{n+1} / (n+1)} has positive lower
asymptotic density: 0 < liminf_{N → ∞} |A ∩ [1,N]| / N. -/
theorem reading_O56_cor2
    (p : ℕ → ℕ)
    (hprime : ∀ n, 1 ≤ n → (p n).Prime)
    (hmono : ∀ m n, 1 ≤ m → m < n → p m < p n)
    (honto : ∀ q, q.Prime → ∃ n, 1 ≤ n ∧ p n = q) :
    0 < Filter.liminf
      (fun N : ℕ =>
        ((((Finset.Icc 1 N).filter
            (fun n => (p n : ℝ) / (n : ℝ) < (p (n + 1) : ℝ) / ((n : ℝ) + 1))).card : ℕ) : ℝ)
          / (N : ℝ))
      atTop := by
  sorry

end ReaderC

/-
## Comment block: ambiguities and choices (reader C, O56)

1. Prime sequence. p_n is indexed from 1 (p 1 = 2). I did not use Nat.nth. Instead p is a
   variable with three hypotheses: every p n (n ≥ 1) is prime, p is strictly increasing on
   indices ≥ 1, and every prime occurs at some index ≥ 1. These determine p on n ≥ 1 uniquely
   and the usual enumeration satisfies them, so they are not vacuous. p 0 is never used.

2. Lower asymptotic density. The text's definition liminf_{N→∞} |A ∩ [1,N]| / N is written as
   Filter.liminf over atTop in ℝ of ((card of filter of Icc 1 N) : ℝ) / N. The sequence lies in
   [0,1]. At N = 0 Lean gives 0/0 = 0; this is the only division-by-zero value, it is in range,
   and it does not affect atTop. So the liminf is a genuine liminf, not a junk value.
   "Positive lower density" is read as 0 < liminf.

3. Corollary's set. A = {n ≥ 1 : p_n/n < p_{n+1}/(n+1)}; its trace on [1,N] is the filter of
   Finset.Icc 1 N, which is exact because A ⊆ [1,∞). The ratio is real division, with n+1 written
   as (n : ℝ) + 1. The text's proof is not formalized, only the statement.

4. Theorem 1.1 quantifier order. "For every fixed real C > 0, there are constants c(C) > 0 and
   N₀(C)" is read as ∀ C > 0, ∃ c > 0, ∃ N₀, ∀ N ≥ N₀. The constants may depend on C (and on the
   fixed prime sequence) but not on N. The count is over 1 ≤ n ≤ N as in the text.

5. Gap condition. p_{n+1} - p_n > C log p_n is written in ℝ with the subtraction in ℝ, so there is
   no truncated ℕ subtraction. Log is Real.log. The ℕ→ℝ casts are explicit.

6. Avoided: ℕ subtraction, x/0 used as a meaningful value, sSup/sInf/iSup, ⊤/⊥, Nat.nth,
   tsum/tprod. Decidability of the filter predicates comes from Real's decidable order.

7. Not formalized: nothing in the O56 statements was left out. The text's proof and the
   assertion "answering a question of Erdős and Prachar" are commentary, not claims formalized here.

Status: the file is written; compile status is reported in the handback.
-/
