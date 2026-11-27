import Mathlib

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
