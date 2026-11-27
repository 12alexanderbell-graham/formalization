import Mathlib

open Real

namespace ReaderA

/-- `A` contains a nonconstant `k`-term arithmetic progression `a, a+d, …, a+(k-1)d` with
`d > 0`. -/
def HasNonconstAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

open Classical in
/-- `r_k(N)`: the largest cardinality of a subset of `[N] = {1, …, N}` containing no nonconstant
`k`-term arithmetic progression. -/
noncomputable def r (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter
    (fun A : Finset ℕ => ¬ HasNonconstAP (↑A : Set ℕ) k)).sup (fun A : Finset ℕ => A.card)

/-- Theorem 1.1, density bound. -/
theorem reading_thm_1_1 (k : ℕ) (hk : 3 ≤ k) :
    ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
      ∀ N : ℕ, 2 ≤ N →
        (r k N : ℝ) ≤ C * N * exp (-c * (log N) ^ ε) := sorry

/-- Theorem 1.1, "Equivalently" threshold form. -/
theorem reading_thm_1_1_threshold (k : ℕ) (hk : 3 ≤ k) :
    ∃ Ak : ℝ, 1 ≤ Ak ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (α : ℝ), 0 < α → α ≤ 1 →
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → α * N ≤ (A.card : ℝ) →
          Ak * (2 + log (1 / α)) ^ Ak ≤ log N →
            HasNonconstAP (↑A : Set ℕ) k := sorry

/-- Corollary 1.2 (divergent reciprocal sums). -/
theorem reading_cor_1_2 (A : Set ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hdiv : ∑' a : A, ((a : ℕ) : ENNReal)⁻¹ = ⊤) :
    ∀ k : ℕ, HasNonconstAP A k := sorry

end ReaderA

/-
Ambiguities and choices (Reader A):

1. Progressions: `a, a+d, …, a+(k-1)d` with `d > 0` is encoded as `∃ a d, 0 < d ∧ ∀ i < k,
   a + i*d ∈ A` over ℕ (all relevant sets are sets of positive integers, so ℕ arithmetic is exact:
   only addition and multiplication, no truncated subtraction; `k-1` is avoided by `i < k`).
2. `r_k(N)`: the maximum, over subsets of `Finset.Icc 1 N`, of the cardinality of AP-free ones,
   via `Finset.sup card` over the (finite) filtered powerset. The empty set is always AP-free
   (for k ≥ 1), so this is a genuine maximum, not a junk `sup ∅` (and `Finset.sup` on ℕ has ⊥ = 0
   anyway). The source defines it for N ≥ 1 and k ≥ 3; the Lean function is total but only used
   with k ≥ 3, N ≥ 1 (N ≥ 2 in the bound).
3. Theorem 1.1: constants `C_k, c_k, ε_k > 0` depend only on k (existential after `k`), uniform in
   `N ≥ 2`. `(log N)^ε` is `Real.rpow` of `log N ≥ log 2 > 0`, so no junk from logs of small
   numbers or rpow of negatives.
4. "Equivalently": stated as a separate theorem, not as an iff with Theorem 1.1. "α-dense subset
   of [N]": `A ⊆ [N]` with `|A| ≥ α N`. Threshold `log N ≥ A_k (2 + log(1/α))^{A_k}` with
   `0 < α ≤ 1`; `1/α` is fine since `α > 0`, `log(1/α) ≥ 0`, so the base is ≥ 2 and rpow is
   well-behaved. `A_k ≥ 1` real (exponent may be non-integer; rpow). I require `N ≥ 1` as in the
   source's range of `r_k`; it is in any case forced since the right side is ≥ 2 > log 0 = 0.
5. Corollary 1.2: `A ⊆ ℕ` with `∑ 1/a = ∞`. The sum is taken in `ENNReal` so "= ∞" is literal
   (in ℝ, `tsum` of a non-summable family is junk 0). To avoid the junk `0⁻¹ = ∞` in ENNReal, I
   assume all elements are positive (the source's opening sentence speaks of sets of positive
   integers, and `1/0` is undefined). "Every finite length" is all `k : ℕ` (including 0, 1, 2;
   the source's proof treats 1 and 2 explicitly), with nonconstant meaning `d > 0`.
6. Logs are natural (`Real.log`), as stated.
-/

namespace ReaderB

open scoped Classical

/-- `S ⊆ ℕ` contains a nonconstant `k`-term arithmetic progression `a, a+d, …, a+(k-1)d`, `d > 0`. -/
def HasAP (k : ℕ) (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ S

/-- `r_k(N)`: largest cardinality of a subset of `{1,…,N}` with no nonconstant `k`-AP
(max over a finite nonempty family: the empty set always qualifies). -/
noncomputable def r (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun S : Finset ℕ => ¬ HasAP k (S : Set ℕ))).sup Finset.card

/-- Theorem 1.1, density bound. -/
theorem readingDensityBound :
    ∀ k : ℕ, 3 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
      ∀ N : ℕ, 2 ≤ N → (r k N : ℝ) ≤ C * N * Real.exp (-c * (Real.log N) ^ ε) := sorry

/-- Theorem 1.1, "equivalently" threshold form. -/
theorem readingThreshold :
    ∀ k : ℕ, 3 ≤ k → ∃ A : ℝ, 1 ≤ A ∧
      ∀ (N : ℕ) (α : ℝ), 1 ≤ N → 0 < α → α ≤ 1 →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → α * N ≤ (S.card : ℝ) →
          Real.log N ≥ A * (2 + Real.log (1 / α)) ^ A →
          HasAP k (S : Set ℕ) := sorry

/-- Corollary 1.2. -/
theorem readingReciprocal (A : Set ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hdiv : ¬ Summable (fun a : A => 1 / (a : ℝ))) :
    ∀ k : ℕ, HasAP k A := sorry

end ReaderB

/-
Ambiguities / choices.
* r_k(N): max of card over AP-free subsets of {1..N}, as Finset.sup over a filtered powerset (ℕ-valued);
  well-defined since ∅ is in the family, no sSup. Defined for all N, k (only used k ≥ 3, N ≥ 2).
* AP: a, d naturals, d > 0, all i < k: a + i*d ∈ S (no subtraction; elements of subsets of [N] are ℕ).
* Thm 1.1: constants C,c,ε real > 0 depending on k; log N is Real.log of a cast, N ≥ 2 so log N > 0
  (real power (log N)^ε via rpow is non-junk). Bound: r ≤ C * N * exp(-c * (log N)^ε).
* Threshold form: "α-dense subset of [N]" = card S ≥ α N, 0<α≤1; N ≥ 1 assumed (N=0 would make log 0 = 0
  junk; with N ≥ 1 hypotheses are vacuous at N=1). log(1/α) with α>0 is nonjunk, ≥ 0. A real, A ≥ 1,
  exponent real (rpow). Conclusion: nonconstant k-AP in S. (k ≥ 3 fixed as in source.)
* Corollary: A ⊆ ℕ; the source says "set of positive integers" in the intro, "A ⊆ ℕ" in the statement,
  so I assume all elements positive (otherwise 1/0 junk for a = 0). Divergence = ¬Summable of
  nonnegative terms (equivalent to sum = ∞). Conclusion for every length k (k = 0,1,2 trivially included),
  nonconstant means d > 0. Source's ℕ may be {1,2,...}; chose to require positivity as hypothesis.
-/

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
