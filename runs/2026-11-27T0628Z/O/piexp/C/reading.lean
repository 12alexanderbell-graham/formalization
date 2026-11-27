import Mathlib

/-!
Reading C, family O9: "The irrationality exponent of π is 2".
-/

/-- The irrationality exponent of x as defined in the source:
μ(x) = sup {ν > 0 : 0 < |x - p/q| < q^{-ν} for infinitely many coprime p, q ∈ ℤ with q ≥ 2}.
The supremum is taken in `ℝ≥0∞`, so an unbounded set gives ∞ rather than a junk value.
The empty supremum is ⊥ = 0 in `ℝ≥0∞`; for irrational x the set contains ν = 1 by Dirichlet's
theorem, so this case does not arise for the irrational numbers the source considers. -/
noncomputable def irrExp (x : ℝ) : ENNReal :=
  ⨆ (ν : ℝ) (_ : 0 < ν ∧ Set.Infinite {pq : ℤ × ℤ | 2 ≤ pq.2 ∧ Int.gcd pq.1 pq.2 = 1 ∧
      0 < |x - (pq.1 : ℝ) / (pq.2 : ℝ)| ∧
      |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (pq.2 : ℝ) ^ (-ν)}),
    ENNReal.ofReal ν

/-- Theorem 1.1 of the source. (a) The irrationality exponent of π is 2 (the sentence
`μ(π) = 2`). (b) The "more precisely" inequality: for every real ν > 2 there is an integer
Q(ν) such that |π - p/q| ≥ q^{-ν} for all integers p and q with q ≥ Q(ν). -/
theorem reading_thm1 :
    irrExp Real.pi = 2 ∧
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, ∀ p q : ℤ, Q ≤ q → 0 < q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  sorry

/-- The abstract's consequence: the Flint–Hills series Σ_{n≥1} 1/(n³ sin² n) (angles in
radians) converges. Summable is used for the nonnegative terms, where summability is
equivalent to convergence of the partial sums. The index is shifted to start at 1. -/
theorem reading_corollary_flint_hills :
    Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 3 * (Real.sin ((n + 1 : ℕ) : ℝ)) ^ 2)) := by
  sorry

/-!
Comments on choices and ambiguities.

* μ(x) is defined in `ℝ≥0∞` as a supremum over ν > 0 in the source's set. This avoids the
  ℝ-valued `sSup` junk value on unbounded sets (a Liouville-type number has μ = ∞).
* The set condition "for infinitely many coprime p, q ∈ ℤ, q ≥ 2" is `Set.Infinite` of pairs
  (p, q) with `2 ≤ q`, `Int.gcd p q = 1`, and `0 < |x - p/q| < q^{-ν}`. The positivity
  `0 < |x - p/q|` is kept as in the source. The rpow base q is ≥ 2, so no rpow of negatives
  arises.
* "The irrationality exponent of π is 2" is `irrExp π = 2`. The source calls this the main
  result, so it is stated, not assumed.
* The "more precisely" inequality: the source says "for every real ν > 2, there is an integer
  Q(ν)" with "q ≥ Q(ν)" and no sign condition on q. Since q^{-ν} is not meaningful for q ≤ 0
  in ℝ, I added `0 < q` as an explicit hypothesis. The source's `p, q` are unrestricted
  integers, and `p` is unconstrained, as written. The inequality is not claimed for reduced
  fractions only, matching "whether or not the fraction is reduced".
* Flint–Hills: "converges" is `Summable` of the shifted series, with angles in radians
  (`Real.sin` takes radians). The denominators are nonzero because sin n ≠ 0 for every
  positive integer n (π is irrational), so no `1/0 = 0` junk is used; that fact is not
  needed to state the claim.
* Proved vs stated: the source's Theorem 1.1 is the main result. The Flint–Hills statement is
  presented as "Corollary" with the abstract saying it is "a consequence"; the excerpt I read
  (lines 40–95 of the TeX) does not show its proof, so I record it as a stated consequence,
  not an independently verified proof. The Alekseyev bound μ(π) ≤ 5/2 is cited, not stated
  here.
* The excerpt begins at `\maketitle`, and the introduction's definition, theorem and
  corollary are visible in full. Nothing else is needed for the statements above.
-/
