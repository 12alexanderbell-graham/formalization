import Mathlib

namespace ReaderC

/-- Theorem 1.1 (logarithmic Landau–Siegel zero bound): there is an absolute `c > 0` such that
every real zero `β ∈ (0,1)` of every primitive nonprincipal real Dirichlet L-function of conductor
`q ≥ 3` satisfies `(1 - β) log q ≥ c`. -/
theorem reading_thm_1_1_landau_siegel :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        DirichletCharacter.IsPrimitive χ → χ ≠ 1 → 3 ≤ q →
        (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 →
          DirichletCharacter.LFunction χ (β : ℂ) = 0 →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  sorry

/-
Ambiguities and choices (Landau–Siegel family, source lines 49-73 of paper.tex):

* L(s, χ): the source defines it by the series for Re s > 1 and "its analytic continuation
  elsewhere". I use `DirichletCharacter.LFunction χ`, the Mathlib function for
  `χ : DirichletCharacter ℂ q`. Its docstring says it is "the unique meromorphic function ℂ → ℂ
  which agrees with ∑ χ n / n^s wherever the latter is convergent", and the lemma
  `DirichletCharacter.LFunction_eq_LSeries` (Mathlib/NumberTheory/LSeries/DirichletContinuation.lean)
  checks agreement with the naive series for Re s > 1. So it is the source's continuation.
* Conductor q: `DirichletCharacter.IsPrimitive χ` means `conductor χ = q` (Mathlib's
  `IsPrimitive` in NumberTheory/DirichletCharacter/Basic.lean). The modulus is q itself, with
  `[NeZero q]` as needed for `DirichletCharacter ℂ q`.
* "Primitive nonprincipal": `χ ≠ 1` is included as in the source's "nonprincipal"; with
  `3 ≤ q` primitivity already forces nonprincipality, so this is redundant but harmless.
* "Real character": every value is real, `∀ a : ZMod q, (χ a).im = 0`. Non-unit values are 0,
  which are real, so this is the usual real-valued condition.
* "Real zero β ∈ (0,1)": `0 < β`, `β < 1` in ℝ and `LFunction χ (β : ℂ) = 0`.
* Conclusion: `(1 - β) * log q ≥ c` with `Real.log (q : ℝ)`, and `c` an absolute constant:
  `∃ c : ℝ, 0 < c ∧ ∀ q χ ...`. The constant is chosen before q, χ, β (uniform in q and χ).
* The statement is for all q ≥ 3 with `3 ≤ q`; the source's `q ≥ 3` is `3 ≤ q` in ℕ.
* The region displayed in the source's introduction (zero-free region) is background, not part
  of Theorem 1.1, so it is not formalized.
-/

end ReaderC
