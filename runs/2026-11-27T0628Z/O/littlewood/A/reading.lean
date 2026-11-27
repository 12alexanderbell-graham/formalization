import Mathlib

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
