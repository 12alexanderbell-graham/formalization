import Mathlib

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
