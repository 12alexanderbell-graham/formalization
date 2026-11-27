import Mathlib

namespace ReaderA

/-!
# Blind reading (reader A): O15 "Asymptotically minimal maxima of real Littlewood
polynomials", Theorem 1.1

Source: `littlewood/sources/introduction_lines1-36.tex`.
-/

namespace ReadingO15

open Filter Topology Complex

/-- `e(t) = exp(2π i t)`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The Littlewood polynomial `P(z) = ∑_{k=0}^{N-1} ε_k z^k`, with signs `ε_k ∈ {-1,1}`
encoded as units of `ℤ` (which are exactly `1` and `-1`). -/
noncomputable def P {N : ℕ} (ε : Fin N → ℤˣ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (((ε k : ℤ) : ℂ)) * z ^ (k : ℕ)

/-- Maximum modulus `‖P‖_∞ = max_{t ∈ 𝕋} |P(e(t))|`. Parametrised by `t : ℝ`; since `e` is
1-periodic this is the same as `t ∈ 𝕋 = ℝ/ℤ`. The function is bounded (by `N`), so the
real `iSup` is the true maximum (no junk value). -/
noncomputable def supNorm {N : ℕ} (ε : Fin N → ℤˣ) : ℝ :=
  ⨆ t : ℝ, ‖P ε (e t)‖

/-- `m_N = min_{ε ∈ {-1,1}^N} (1/√N) ‖∑ ε_k z^k‖_∞`, a genuine minimum over the finite
nonempty set of sign vectors. -/
noncomputable def m (N : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ε : Fin N → ℤˣ => (1 / Real.sqrt N) * supNorm ε)

/-- Theorem 1.1: `lim_{N→∞} m_N = 1`. -/
theorem reading_O15_limit : Tendsto m atTop (𝓝 1) := by
  sorry

/-- Theorem 1.1, "Equivalently" form: for every `η > 0` there is `N₀` such that for every
integer `N ≥ N₀` there are signs `ε_0, …, ε_{N-1}` with
`max_{|z|=1} |∑ ε_k z^k| ≤ (1+η)√N`. -/
theorem reading_O15_equiv :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ ε : Fin N → ℤˣ, ∀ z : ℂ, ‖z‖ = 1 →
        ‖∑ k : Fin N, ((ε k : ℤ) : ℂ) * z ^ (k : ℕ)‖ ≤ (1 + η) * Real.sqrt N := by
  sorry

end ReadingO15

/-!
## Ambiguities and choices (reader A)

1. *Signs.* `ε_k ∈ {-1,1}` encoded as `ε : Fin N → ℤˣ` (Mathlib has `Fintype ℤˣ` with
   `ℤˣ = {1, -1}`), cast to `ℂ`. "Real coefficients" = these real signs.
2. *Torus and `e`.* `𝕋 = ℝ/ℤ` with `e(t) = exp(2πit)`; I range `t` over `ℝ` instead of the
   quotient, which gives the same maximum by 1-periodicity. Haar measure plays no role in the
   statement.
3. *Max vs sup.* `‖P‖_∞` is written as a real `iSup`; the function `t ↦ |P(e t)|` is
   continuous, periodic and bounded by `N`, so the `iSup` is attained and is not the junk
   value of an unbounded `iSup`.
4. *`m_N` as a minimum.* Implemented with `Finset.inf'` over all `2^N` sign vectors (nonempty
   for every `N`, including `N = 0` where there is the single empty vector), so it is an
   actual minimum, not a junk `sInf`.
5. *`N = 0`.* `1/√0 = 0` in Lean, so `m_0 = 0`; the source's `m_N` is only meaningful for
   `N ≥ 1`. This affects only one term and is irrelevant to the limit statement.
6. *Limit.* `lim_{N→∞} m_N = 1` read as `Tendsto m atTop (𝓝 1)` over `N : ℕ` (all lengths,
   not a subsequence, as the source stresses).
7. *"Equivalently" form.* `max_{|z|=1} |…| ≤ (1+η)√N` encoded as the pointwise bound for all
   `z` with `‖z‖ = 1` (equivalent to the bound on the max, and avoids any sup). `N₀` and `N`
   are natural numbers ("every integer `N ≥ N₀`"; `N` is a length). `√N` is `Real.sqrt`.
8. The two forms are stated as separate theorems; I did not state or prove their equivalence
   (the source asserts it; it uses `m_N ≥ 1`).
-/
end ReaderA

namespace ReaderB

open Filter Topology Complex

/-- Sign vectors of length `N` (real coefficients ±1). -/
def Signs (N : ℕ) : Type := {ε : Fin N → ℝ // ∀ k, ε k = 1 ∨ ε k = -1}

/-- The polynomial `∑ ε_k z^k`. -/
noncomputable def littlePoly {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)

/-- `‖P‖_∞ = max_{t ∈ ℝ/ℤ} |P(e(t))|`, taken as a sup over `t : ℝ` (1-periodic). -/
noncomputable def supNorm {N : ℕ} (ε : Fin N → ℝ) : ℝ :=
  ⨆ t : ℝ, ‖littlePoly ε (Complex.exp (2 * Real.pi * Complex.I * t))‖

/-- `m_N = min over signs of ‖P‖_∞ / √N` (as an infimum). -/
noncomputable def mN (N : ℕ) : ℝ :=
  ⨅ ε : Signs N, supNorm ε.1 / Real.sqrt N

theorem reading_littlewood_limit : Tendsto mN atTop (𝓝 1) := sorry

theorem reading_littlewood_equiv :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ ε : Fin N → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)‖ ≤ (1 + η) * Real.sqrt N := sorry

/-
Ambiguities / choices:
* Signs as functions Fin N → ℝ with values ±1 (subtype `Signs N`); polynomial evaluated over ℂ.
* "max over t ∈ T": written as iSup over t : ℝ of |P(exp(2πit))|; by periodicity equals the max over T.
  The set is bounded above (by N) so iSup is the honest sup; no junk. It is a max in fact (continuity, compact).
* "min over signs": iInf over the finite nonempty (for N ≥ 1) type Signs N, so a genuine min. For N = 0
  the type has one element, sup over an empty-sum polynomial is 0, and 0/√0 = 0: junk at N = 0 only, irrelevant
  to the limit. Real.sqrt used for √N.
* Limit as N → ∞ over ℕ (atTop), target 1.
* Equivalent form: stated directly with |z| = 1 (all z, not only e(t)), "N ≥ N₀" over ℕ, as in source.
  Source says `≤ (1+η)√N`, same here.
* No requirement that equivalence be derived; both are separate theorems.
-/
end ReaderB

namespace ReaderC

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
end ReaderC
