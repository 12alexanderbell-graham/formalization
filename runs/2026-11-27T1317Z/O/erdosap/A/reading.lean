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
