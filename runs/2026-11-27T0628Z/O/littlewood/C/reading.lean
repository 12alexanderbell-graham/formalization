import Mathlib

namespace ReadingC

/-- Real sign vector of length N: each coefficient ε_k (k < N) lies in {1, -1}. -/
def IsSignVec (N : ℕ) (ε : ℕ → ℝ) : Prop :=
  ∀ k < N, ε k = 1 ∨ ε k = -1

/-- ‖P‖_∞ = max_{t ∈ T} |P(e(t))| for P(z) = ∑_{k<N} ε_k z^k, with e(t) = exp(2πi t).
Taken as sSup over t ∈ [0,1] (the circle T = ℝ/ℤ is parametrised by [0,1]). -/
noncomputable def lwMaxMod (N : ℕ) (ε : ℕ → ℝ) : ℝ :=
  sSup ((fun t : ℝ =>
      ‖∑ k ∈ Finset.range N,
          ((ε k : ℝ) : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) ^ k‖)
    '' Set.Icc (0 : ℝ) 1)

/-- m_N = min over real sign vectors of (1/√N) ‖∑ ε_k z^k‖_∞. Taken as sInf over the
image of the sign vectors; the minimum is attained since the set is finite-valued,
but sInf is used so no attainment is assumed. -/
noncomputable def lwMN (N : ℕ) : ℝ :=
  sInf ((fun ε : ℕ → ℝ => (1 / Real.sqrt (N : ℝ)) * lwMaxMod N ε) '' {ε | IsSignVec N ε})

/-- Theorem 1.1, limit form: for Littlewood polynomials with real coefficients, lim m_N = 1. -/
theorem reading_littlewood_limit :
    Filter.Tendsto lwMN Filter.atTop (nhds 1) := sorry

/-- Theorem 1.1, "Equivalently" form: for every η > 0 there is N_0 such that for every
integer N ≥ N_0 there are real signs ε_0..ε_{N-1} with max_{|z|=1} |∑ ε_k z^k| ≤ (1+η)√N. -/
theorem reading_littlewood_equiv :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∃ ε : ℕ → ℝ, IsSignVec N ε ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          ‖∑ k ∈ Finset.range N, ((ε k : ℝ) : ℂ) * z ^ k‖ ≤ (1 + η) * Real.sqrt (N : ℝ) :=
  sorry

end ReadingC

/-
Ambiguities and choices (reader C):

1. Circle T = ℝ/ℤ with e(t) = exp(2πit). The max over |z| = 1 is written as sSup over
   t ∈ [0,1] of |P(e(t))|. Equivalent to the max over the circle by periodicity and
   continuity, but I chose the t-parametrised form for lwMaxMod, while the "Equivalently"
   theorem uses the literal ∀ z with ‖z‖ = 1 (no parametrisation).

2. Littlewood polynomial of length N: coefficients ε_0..ε_{N-1}, so the sum is over
   range N. Coefficients are stored as ε : ℕ → ℝ, and only the values at k < N matter
   (IsSignVec constrains only k < N). Junk values outside range N are ignored by the sums.

3. "real coefficients" = real sign vector: ε_k ∈ {1, -1}. Coefficients cast to ℂ.

4. m_N: min over sign vectors of (1/√N) * ‖P‖_∞. I used sInf (not a min), so no
   attainment is built in; the source's min is equal to sInf since the image is finite-
   valued. The norm of P is lwMaxMod, a sSup over t ∈ [0,1], which exists (continuous on a
   compact set).

5. Ground-level detail: N is ℕ; N = 0 gives sqrt 0 = 0 and division by zero yields junk
   (1/0 = 0 in Lean). This affects only the value of lwMN 0, not the limit statement.

6. "m_N ≥ 1" (orthogonality) is stated in the source but not as a theorem here; not part
   of Theorem 1.1.

7. The "Equivalently" statement: "for every η > 0 there is N0 such that for every integer
   N ≥ N0 there are signs with max ≤ (1+η)√N". I wrote η : ℝ with 0 < η (no upper bound,
   as the source does not state one). Strict vs non-strict inequalities: the source uses ≤.

8. The source's "lim m_N = 1" is Filter.Tendsto lwMN atTop (nhds 1).
-/
