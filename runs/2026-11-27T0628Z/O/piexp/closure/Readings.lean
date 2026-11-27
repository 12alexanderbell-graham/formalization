import Mathlib

namespace ReaderA

/-!
# Blind reading (reader A), family O9 "piexp"

Source: `piexp/sources/main_lines40-95.tex` (abstract, Introduction, Theorem 1.1 = `thm:main`,
Corollary `thm:flinthills`).
-/

open Filter Topology

namespace ReadingA.PiExp

/-- The set from the source's definition of `μ(x)`:
`{ν > 0 : 0 < |x - p/q| < q^{-ν} for infinitely many coprime p, q ∈ ℤ, q ≥ 2}`.
"Infinitely many coprime p, q" = the set of such pairs `(p, q)` is infinite. Since `q ≥ 2`,
the base of `q ^ (-ν)` is positive (no rpow of negatives). -/
def approxExponents (x : ℝ) : Set ℝ :=
  {ν | 0 < ν ∧
    {pq : ℤ × ℤ | IsCoprime pq.1 pq.2 ∧ 2 ≤ pq.2 ∧
        0 < |x - (pq.1 : ℝ) / pq.2| ∧ |x - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-ν)}.Infinite}

/-- Irrationality exponent `μ(x) = sup (approxExponents x)`, taken in `EReal` (a complete
lattice), so the value is meaningful even if the set is unbounded (`μ = ⊤`) or empty (`μ = ⊥`);
no junk `sSup`. The source defines `μ(x)` for irrational `x`. -/
noncomputable def irrationalityExponent (x : ℝ) : EReal :=
  sSup ((fun ν : ℝ => (ν : EReal)) '' approxExponents x)

/-- Theorem 1.1, first sentence: "The irrationality exponent of π is 2." -/
theorem readingPiExp_mu : irrationalityExponent Real.pi = 2 := by
  sorry

/-- Same sentence, stated without any `sSup` at all: `2` is the least upper bound in `ℝ` of the
defining set (equivalent to `readingPiExp_mu`, since the set is nonempty for irrational `x`). -/
theorem readingPiExp_mu_isLUB : IsLUB (approxExponents Real.pi) 2 := by
  sorry

/-- Theorem 1.1, "More precisely": for every real `ν > 2` there is an integer `Q(ν)` such that
`|π - p/q| ≥ q^{-ν}` for all `p ∈ ℤ`, `q ∈ ℤ`, `q ≥ Q(ν)`.
The guard `0 < q` avoids rpow of a nonpositive base; it is harmless because the property is
monotone in `Q`, so this is equivalent to asking for some `Q ≥ 1`. -/
theorem readingPiExp_precise :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, ∀ p q : ℤ, 0 < q → Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / q| := by
  sorry

/-- The Flint–Hills term `1 / (n^3 sin^2 n)` (angles in radians). For `n ≥ 1`, `sin n ≠ 0`
since `π` is irrational, so the division is genuine (no division-by-zero junk) on the range
summed. -/
noncomputable def flintHillsTerm (n : ℕ) : ℝ :=
  1 / ((n : ℝ) ^ 3 * Real.sin n ^ 2)

/-- Corollary (`thm:flinthills`) / abstract: "the classical Flint–Hills series
`∑_{n ≥ 1} 1/(n^3 sin^2 n)` converges", read literally as convergence of the partial sums
`∑_{n=1}^{N}` to a finite real limit (no `tsum`). -/
theorem readingPiExp_flintHills :
    ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, flintHillsTerm n) atTop (𝓝 L) := by
  sorry

/-- Equivalent `Summable` form of the corollary (terms are nonnegative, so convergence of
partial sums ⇔ summability), indexed from `n = 1` via `n + 1`. -/
theorem readingPiExp_flintHills_summable :
    Summable (fun n : ℕ => flintHillsTerm (n + 1)) := by
  sorry

end ReadingA.PiExp

/-!
## Ambiguities and choices

1. **Definition of μ(x).** Taken verbatim: `ν > 0`, `0 < |x - p/q| < q^{-ν}`, infinitely many
   coprime `(p, q) ∈ ℤ × ℤ` with `q ≥ 2`. "Infinitely many coprime p, q" is read as infinitely
   many pairs. Coprimality is `IsCoprime` on `ℤ` (⇔ `Int.gcd p q = 1`). The source restricts the
   definition to irrational `x`; I define it for all real `x` and only apply it to `π`
   (irrational, `Real.irrational_pi`).
2. **sup.** The set may be unbounded (Liouville numbers) in general, so `sSup` in `ℝ` would be
   junk; I take `sSup` in `EReal`. I also give the `sSup`-free form `IsLUB (approxExponents π) 2`.
   For irrational `x` the set contains `(0, 2)` (Dirichlet), so the two are equivalent.
3. **"More precisely".** `Q(ν)` is an integer; I quantify `∃ Q : ℤ` and add `0 < q` so that
   `(q : ℝ) ^ (-ν)` never has a nonpositive base. Because the conclusion only gets weaker for
   larger `Q`, this is equivalent to the source's statement with `Q ≥ 1`. As the source stresses,
   `p, q` are arbitrary integers, not necessarily coprime; the fraction is `(p : ℝ) / q`.
   Ineffectivity of `Q(ν)` is not expressible and is not formalized.
4. **Flint–Hills convergence.** "Converges" read as: partial sums `∑_{n=1}^N` tend to a finite
   real limit. Also given in `Summable` form; with nonnegative terms these agree. No `tsum` is
   used. `sin` is `Real.sin` (radians). The `n = 0` term is excluded (Icc 1 N, and `n+1` in the
   summable form); at `n = 0` Lean's `1/0 = 0` would be junk, which is why it is excluded.
5. No ℕ subtraction is used; rpow bases are always `≥ 1` or `≥ 2`.

## Proved vs stated
* Theorem 1.1 (μ(π) = 2 and the "more precisely" inequality) is the main result, claimed proved
  ("Our main result proves it"); the excerpt contains only the statement.
* The Flint–Hills corollary is stated as a consequence ("As a consequence"); the excerpt does not
  contain its proof. It cites Alekseyev's result relating convergence to `μ(π)` (only the
  necessity direction, "convergence requires μ(π) ≤ 5/2", is visible before the excerpt is cut
  off), so the corollary's derivation presumably also uses an Alekseyev-type sufficiency
  criterion not shown in the excerpt.
* "The pigeonhole principle gives μ(x) ≥ 2" is a standard background fact, not formalized.
-/
end ReaderA

namespace ReaderB

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
end ReaderB

namespace ReaderC

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
end ReaderC
