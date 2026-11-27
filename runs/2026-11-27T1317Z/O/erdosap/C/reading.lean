import Mathlib

namespace ReaderC

/-- `S` contains a nonconstant `k`-term progression `a, a+d, …, a+(k-1)d` with `d > 0`. -/
def HasNonconstAP (k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

open scoped Classical in
/-- `r_k(N)`: the largest cardinality of a subset of `[N] = {1, …, N}` with no nonconstant
`k`-term progression. The maximum is over a finite nonempty family (`∅` is admissible), so
`Finset.sup` is used instead of `sSup`. -/
noncomputable def rk (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun S => ¬ HasNonconstAP k S)).sup Finset.card

/-- Theorem 1.1: for each `k ≥ 3` there are constants `C, c, ε > 0` with
`r_k(N) ≤ C N exp(-c (log N)^ε)` for every `N ≥ 2`. Natural logarithms (`Real.log`). -/
theorem reading_ap_thm1 : ∀ k : ℕ, 3 ≤ k →
    ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
      ∀ N : ℕ, 2 ≤ N →
        (rk k N : ℝ) ≤ C * (N : ℝ) * Real.exp (-(c * (Real.log (N : ℝ)) ^ ε)) := by
  sorry

/-- Theorem 1.1, "Equivalently" threshold form: for each `k ≥ 3` there is `A ≥ 1` such that any
`α`-dense subset `S ⊆ [N]` (`|S| ≥ α N`, `0 < α ≤ 1`) with
`log N ≥ A (2 + log(1/α))^A` contains a nonconstant `k`-term progression. -/
theorem reading_ap_thm1_threshold : ∀ k : ℕ, 3 ≤ k →
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ N : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 →
        A * (2 + Real.log (1 / α)) ^ A ≤ Real.log (N : ℝ) →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → α * (N : ℝ) ≤ (S.card : ℝ) →
          HasNonconstAP k S := by
  sorry

/-- Corollary 1.2: if `A` is a set of positive integers with divergent reciprocal sum
(`¬ Summable (1/a)` on `A`, i.e. the sum of nonnegative terms is infinite), then for every
finite length `k` there are `a` and `d > 0` with `a, a+d, …, a+(k-1)d ∈ A`. -/
theorem reading_ap_cor2 : ∀ A : Set ℕ, (∀ a ∈ A, 0 < a) →
    ¬ Summable (fun a : A => (1 : ℝ) / (a : ℝ)) →
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  sorry

end ReaderC

/-
Comment block: ambiguities and choices.

1. Progressions: `a, a+d, …, a+(k-1)d` with `a, d` natural numbers and `d > 0` (nonconstant).
   Since all terms lie in `[N] ⊆ ℕ`, restricting `a` to ℕ loses nothing. The source's `d > 0` is
   kept.

2. `r_k(N)`: defined as `Finset.sup` of cardinalities over the finite family of subsets
   `S ⊆ Icc 1 N` with no nonconstant k-term progression in `S`. This avoids `sSup ∅`; the family
   contains `∅`, so it is nonempty, and `Finset.sup` on ℕ returns the max. `HasNonconstAP` is
   written with `∃`, and the filter uses classical decidability (`open Classical`), which only
   affects computability, not meaning. The source's `[N] = {1, …, N}` is `Finset.Icc 1 N`.

3. Constants: `C_k, c_k, ε_k` are real and strictly positive, as stated in the source. The
   expression `(Real.log N) ^ ε` is real `rpow`; for `N ≥ 2` the log is positive, so it is
   well defined and the power is the intended one. `N ≥ 2` is an explicit hypothesis (the source
   says `N ≥ 2`).
   The `exp(-c (log N)^ε)` form is the source's `exp(-c_k (log N)^{ε_k})`.

4. Threshold form: `A_k ≥ 1` is taken real (the source does not say integer). "α-dense subset of
   [N]" is taken as `|S| ≥ α N` with `S ⊆ [N]`; the source does not define it further, so this is
   my choice. The hypothesis `log N ≥ A (2 + log(1/α))^A` uses real `rpow` for the power, with
   base `2 + log(1/α) ≥ 2 > 0`, so no junk. `log(1/α)` with `0 < α ≤ 1` is well defined and
   nonnegative. The conclusion is that `S` contains a nonconstant k-term progression, expressed
   as `HasNonconstAP k S`. Since `N` is a natural number and `log` is `Real.log` of its cast, `N
   = 0, 1` give `log N ≤ 0`, so the hypothesis fails for them and nothing is claimed; no junk.

5. Corollary 1.2: `A ⊆ ℕ` is taken as a set of POSITIVE integers. The source's intro says
   "a set A of positive integers", but the corollary says `A ⊆ ℕ`. With `0 ∈ A`, the term
   `1/0` would be junk (`1/0 = 0` in Lean), so I restrict to `0 < a` for `a ∈ A`. This is the
   intro's reading. "Divergent reciprocal sum" is `¬ Summable` of `1/a` over the subtype `A`;
   since terms are nonnegative, non-summability is equivalent to the sum being `+∞`.
   "Nonconstant progressions of every finite length": for each `k : ℕ` (including `k = 1, 2`,
   which the source's proof gets from infinitude of `A`), there are `a` and `d > 0` with
   `a + i d ∈ A` for all `i < k`. For `k = 0` the condition is vacuous.

6. The source's `Corollary 1.2` depends on Theorem 1.1 only through the proof; only the
   statement is formalized here, as requested.
-/
