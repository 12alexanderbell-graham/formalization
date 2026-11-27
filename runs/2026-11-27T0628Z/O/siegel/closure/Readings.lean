import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

open Complex

/-- A Dirichlet character is real if all its values are real numbers. -/
def IsRealChar {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ a : ZMod N, (χ a).im = 0

/-- Sanity check: `DirichletCharacter.LFunction χ` agrees with the Dirichlet series
`∑_{n ≥ 1} χ(n) n^{-s}` on `Re s > 1` ... -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = LSeries (fun n => χ n) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

/-- ... and is entire for nonprincipal `χ`, hence it is the (unique) analytic continuation. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  DirichletCharacter.differentiable_LFunction hχ

/-- Theorem 1.1: there is an absolute constant `c > 0` such that every real zero `β ∈ (0,1)` of
every primitive nonprincipal real Dirichlet `L`-function of conductor `q ≥ 3` satisfies
`(1 - β) log q ≥ c`. -/
theorem reading_thm_1_1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        3 ≤ q → χ.IsPrimitive → χ ≠ 1 → IsRealChar χ →
          ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
            c ≤ (1 - β) * Real.log q := sorry

/-- Variant with the conductor stated explicitly via `DirichletCharacter.conductor`, for a
primitive character of arbitrary modulus `N` (equivalent, since primitive means modulus = conductor). -/
theorem reading_thm_1_1_conductor :
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        χ.IsPrimitive → χ ≠ 1 → IsRealChar χ → 3 ≤ χ.conductor →
          ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
            c ≤ (1 - β) * Real.log χ.conductor := sorry

end ReaderA

/-
Ambiguities and choices (reader A).

1. L(s, χ). The source defines L(s,χ) = ∑ χ(n) n^{-s} for Re s > 1 and "its analytic continuation
   elsewhere". I use `DirichletCharacter.LFunction χ`. How I know it is that continuation:
   - `DirichletCharacter.LFunction_eq_LSeries` (checked above by `example`): it equals
     `LSeries (χ ·) s = ∑ χ(n) n^{-s}` when `1 < Re s`;
   - `DirichletCharacter.differentiable_LFunction` (checked above): for `χ ≠ 1` it is entire.
   An entire function is determined by its values on the open set `{Re s > 1}` (identity theorem,
   ℂ connected), so it is the analytic continuation. (Mathlib's `LSeries` itself is NOT used,
   since it is junk `0` for `Re s ≤ 1`, which is exactly where β lies.)

2. Primitive, conductor q. A primitive character of conductor q is a character mod q whose
   conductor is q; Mathlib's `IsPrimitive χ` is `conductor χ = N`. Main reading: modulus `q`,
   `χ.IsPrimitive`. A variant with arbitrary modulus `N` and `q := χ.conductor` is also stated.
   `[NeZero q]` is needed for `LFunction`; it is implied by `3 ≤ q` anyway.

3. Nonprincipal: `χ ≠ 1` (the trivial character mod q). For primitive χ mod q ≥ 2 this is automatic
   (the trivial character has conductor 1), but the source states it, so it is kept.

4. Real character: all values real, `(χ a).im = 0` for all `a`. (Equivalently χ² = 1, i.e.
   quadratic, for nonprincipal χ; I used the values formulation, the literal meaning of "real".)

5. Real zero β ∈ (0,1): `β : ℝ`, `0 < β < 1`, `LFunction χ (β : ℂ) = 0`. The source says
   "every real zero β ∈ (0,1)", so only zeros in the open interval are constrained.

6. Constant: `∃ c > 0` before all q, χ, β ("absolute"). Inequality `(1-β) log q ≥ c` written as
   `c ≤ (1 - β) * Real.log q`, with `Real.log` of `q ≥ 3` (no junk: log of a positive number;
   `1 - β` is real subtraction, positive).

7. Coefficients: Dirichlet characters are taken with values in ℂ (`DirichletCharacter ℂ q`),
   since L(s,χ) is complex-valued.
-/

-- ===== reader B =====

namespace ReaderB

open DirichletCharacter

/-- Real-valued character. -/
def IsRealChar {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop := ∀ n : ZMod q, (χ n).im = 0

/-- Theorem 1.1 (logarithmic Landau–Siegel exclusion). `L(s,χ)` is `DirichletCharacter.LFunction χ s`. -/
theorem readingMain :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive → χ ≠ 1 → IsRealChar χ →
      ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
        c ≤ (1 - β) * Real.log q := sorry

/- AMBIGUITIES AND CHOICES
* L(s,χ) = `DirichletCharacter.LFunction χ s` (s : ℂ). It is the analytic continuation: Mathlib proves
  `DirichletCharacter.LFunction_eq_LSeries` (equals the Dirichlet series for 1 < re s) and
  `differentiable_LFunction` (entire for χ ≠ 1), so by the identity theorem it is THE continuation.
  Nonprincipality (χ ≠ 1) is a hypothesis, which makes this applicable.
* "Primitive of conductor q": `χ.IsPrimitive` means `conductor χ = q` in Mathlib, with χ a character
  modulo q (level q). `NeZero q` is needed for the type to be nice; implied by 3 ≤ q, but kept as
  an instance argument (harmless since q ≥ 3 is hypothesised).
* Real character: all values have imaginary part 0 (equivalent to χ² = 1 on units; values at
  non-units are 0).
* Real zero β ∈ (0,1): β cast to ℂ, open interval. The inequality (1-β) log q ≥ c written as
  `c ≤ (1-β) * Real.log q`, with q cast ℕ → ℝ. "Absolute constant" is ∃ c outside all quantifiers.
* No junk values: log q with q ≥ 3 is a genuine positive value; 1-β > 0.
-/

end ReaderB

-- ===== reader C =====

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
