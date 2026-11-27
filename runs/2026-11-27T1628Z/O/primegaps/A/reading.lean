import Mathlib

/-!
Blind reading (reader A) of O56, "Positive lower density of large prime gaps":
Theorem 1.1 and Corollary 1.2 of the introduction.
-/

namespace ReaderA

open Filter

/-- `p n` is the `n`-th prime, 1-indexed as in the text (`p 1 = 2`, `p 2 = 3`, ...).
The value `p 0` is a placeholder that is never used: every occurrence below has `n ≥ 1`.
The pattern match avoids writing `Nat.nth Nat.Prime (n - 1)` with ℕ subtraction. -/
noncomputable def p : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.nth Nat.Prime n

/-- Sanity check: the first prime is `2`. -/
lemma p_one : p 1 = 2 := by
  simp [p, Nat.nth_prime_zero_eq_two]

/-- `Nat.nth Nat.Prime` is not a junk value: the set of primes is infinite, so every
`p n` with `n ≥ 1` really is a prime. -/
lemma p_prime (n : ℕ) (hn : 1 ≤ n) : (p n).Prime := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime m

/-- `|A ∩ [1, N]|` for a set `A` of positive integers. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (· ∈ A)).card

/-- The ratio `|A ∩ [1,N]| / N`. (At `N = 0` Lean gives `0/0 = 0`; this single value is
irrelevant to a `liminf` along `atTop`.) -/
noncomputable def densityRatio (A : Set ℕ) (N : ℕ) : ℝ := (countUpTo A N : ℝ) / N

/-- Lower asymptotic density, as the text defines it: `liminf_{N → ∞} |A ∩ [1,N]| / N`. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ := liminf (densityRatio A) atTop

lemma densityRatio_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ densityRatio A N := by
  unfold densityRatio; positivity

lemma densityRatio_le_one (A : Set ℕ) (N : ℕ) : densityRatio A N ≤ 1 := by
  unfold densityRatio countUpTo
  classical
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

/-- The real `liminf` in `lowerDensity` is a genuine `liminf` (not a junk value of `sSup`):
the sequence is bounded below ... -/
lemma densityRatio_isBoundedUnder_ge (A : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (densityRatio A) :=
  isBoundedUnder_of ⟨0, fun N => densityRatio_nonneg A N⟩

/-- ... and cobounded (bounded above by `1`). -/
lemma densityRatio_isCoboundedUnder_ge (A : Set ℕ) :
    IsCoboundedUnder (· ≥ ·) atTop (densityRatio A) :=
  isCoboundedUnder_ge_of_le atTop (fun N => densityRatio_le_one A N)

/-- **Theorem 1.1.** For every fixed real `C > 0` there are constants `c(C) > 0` and `N₀(C)`
such that for every integer `N ≥ N₀(C)`,
`#{1 ≤ n ≤ N : p_{n+1} - p_n > C log p_n} ≥ c(C) N`. -/
theorem reading_thm_1_1 :
    ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤
        (((Finset.Icc 1 N).filter
          (fun n => (p (n + 1) : ℝ) - (p n : ℝ) > C * Real.log (p n))).card : ℝ) := sorry

/-- The set `{n ≥ 1 : p_n / n < p_{n+1} / (n+1)}`. -/
def ratioIncreaseSet : Set ℕ :=
  {n | 1 ≤ n ∧ (p n : ℝ) / (n : ℝ) < (p (n + 1) : ℝ) / ((n : ℝ) + 1)}

/-- **Corollary 1.2.** The set `{n ≥ 1 : p_n/n < p_{n+1}/(n+1)}` has positive lower
asymptotic density. -/
theorem reading_cor_1_2 : 0 < lowerDensity ratioIncreaseSet := sorry

end ReaderA

/-
Ambiguities and choices (reader A)
==================================

1. Indexing of primes. The text writes `p_n` for the n-th prime with `n ≥ 1` (so `p_1 = 2`).
   I defined `p (n+1) := Nat.nth Nat.Prime n` and `p 0 := 0` (placeholder, never used, since
   every occurrence has `n ≥ 1`). `Nat.nth` is not a junk value here because the primes are
   infinite (lemma `p_prime`, proved, not sorried); `p_one` checks `p 1 = 2`.

2. Gaps and subtraction. `p_{n+1} - p_n` is computed after casting to ℝ, so no ℕ-truncation
   can occur (it is positive anyway). The ratios `p_n/n` and `p_{n+1}/(n+1)` are real
   divisions with `n ≥ 1`, so no division by zero.

3. `log` is the natural logarithm `Real.log` applied to `(p n : ℝ) ≥ 2 > 0`, so no junk value
   of `Real.log` on nonpositive arguments arises.

4. Theorem 1.1 quantifiers. "constants c(C) > 0 and N₀(C)" is read as `∀ C > 0, ∃ c > 0,
   ∃ N₀, ∀ N ≥ N₀`. I took `N₀ : ℕ` and `N : ℕ`; the text says "every integer N ≥ N₀(C)";
   taking N₀ natural loses nothing (any real/integer N₀ can be replaced by a larger natural),
   and negative integers N would give an empty count with the trivially true bound
   `0 ≥ c N`. The inequality `p_{n+1} - p_n > C log p_n` is strict, as in the text.
   "≥ c(C) N" is written `c * N ≤ card`.

5. Lower asymptotic density. Defined literally as `liminf_{N → ∞} |A ∩ [1,N]| / N` using
   `Filter.liminf` in ℝ along `atTop` on ℕ. To rule out the junk `sSup` behaviour of
   `liminf` in a conditionally complete lattice, I proved (no sorry) that the ratio sequence
   lies in `[0,1]`, hence is bounded below and cobounded, so the `liminf` is the genuine one.
   The ratio at `N = 0` is the junk `0/0 = 0`, which a `liminf` along `atTop` ignores.
   "Positive lower asymptotic density" is `0 < lowerDensity A`.

6. The set in Corollary 1.2 is a set of positive integers (`n ≥ 1` is part of its
   definition), matching "for a set A of positive integers"; `countUpTo` only counts
   `n ∈ [1, N]` anyway.

7. Not formalized: the proof of the corollary (the reduction via the prime number theorem),
   the abstract's informal phrasing "a positive proportion of consecutive prime gaps exceed
   C log p", and the attribution to Erdős–Prachar; only the two displayed statements are
   stated.
-/
