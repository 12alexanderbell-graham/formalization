import Mathlib

/-!
# Blind reading A of O30: "The subcritical Hénon–Lane–Emden conjecture"

Source: `henon/sources/introduction_lines1-68.tex`, Theorem 1.1 and Corollary 1.2.
-/

namespace ReaderA

open Laplacian

/-- `ℝⁿ`, with its Euclidean norm `|x|`. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The function class `C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)`: twice continuously differentiable on the open set
`ℝⁿ∖{0}` and continuous on all of `ℝⁿ`. -/
def C2offOriginCont {n : ℕ} (u : Rn n → ℝ) : Prop :=
  ContDiffOn ℝ 2 u ({0}ᶜ : Set (Rn n)) ∧ Continuous u

/-- The Hénon–Lane–Emden system (eq:system) at a point `x`:
`-Δu = |x|^A v^p`, `-Δv = |x|^B u^q`. -/
def HenonLaneEmdenAt {n : ℕ} (A B p q : ℝ) (u v : Rn n → ℝ) (x : Rn n) : Prop :=
  -(Δ u) x = ‖x‖ ^ A * (v x) ^ p ∧ -(Δ v) x = ‖x‖ ^ B * (u x) ^ q

/-- Theorem 1.1. Let `n ≥ 2`, `p, q > 0`, `A, B ∈ ℝ` with
`(n+A)/(p+1) + (n+B)/(q+1) > n - 2`. There are no `u, v ∈ C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)` with
`u(x) > 0`, `v(x) > 0` for all `x ∈ ℝⁿ`, satisfying the system at every `x ≠ 0`. -/
theorem reading_thm_1_1 (n : ℕ) (hn : 2 ≤ n) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (A B : ℝ)
    (hsub : ((n : ℝ) + A) / (p + 1) + ((n : ℝ) + B) / (q + 1) > (n : ℝ) - 2) :
    ¬ ∃ u v : Rn n → ℝ,
      C2offOriginCont u ∧ C2offOriginCont v ∧
      (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      ∀ x, x ≠ 0 → HenonLaneEmdenAt A B p q u v x := sorry

/-- Corollary 1.2 (unweighted Lane–Emden conjecture). For every integer `n ≥ 3` and `p, q > 0`
with `1/(p+1) + 1/(q+1) > (n-2)/n`, there is no strictly positive `C²(ℝⁿ)` solution of
`-Δu = v^p`, `-Δv = u^q` in `ℝⁿ`. -/
theorem reading_cor_1_2 (n : ℕ) (hn : 3 ≤ n) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hsub : 1 / (p + 1) + 1 / (q + 1) > ((n : ℝ) - 2) / n) :
    ¬ ∃ u v : Rn n → ℝ,
      ContDiff ℝ 2 u ∧ ContDiff ℝ 2 v ∧
      (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      ∀ x, -(Δ u) x = (v x) ^ p ∧ -(Δ v) x = (u x) ^ q := sorry

end ReaderA

/-!
## Ambiguities and choices

1. *Which Laplacian.* I use `Laplacian.laplacian` (notation `Δ`, after `open Laplacian`) through
   Mathlib's instance `InnerProductSpace.instLaplacian : Laplacian (E → F) (E → F)` for a
   finite-dimensional real inner product space `E` (here `E = EuclideanSpace ℝ (Fin n)`).
   It is `Δ f x = ∑ᵢ D²f(x)(eᵢ, eᵢ)` for any orthonormal basis
   (`laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`), i.e. the usual `∑ᵢ ∂²f/∂xᵢ²` on `ℝⁿ`
   with the standard Euclidean structure. I do not use `laplacianWithin` on `{0}ᶜ`: since
   `{0}ᶜ` is open and `fderiv` is local, the two agree at every `x ≠ 0`, and the global
   operator is the more literal "Δ on ℝⁿ". There is no separate declaration named
   `InnerProductSpace.laplacian` in this Mathlib; the operator is reached through the
   `Laplacian` notation class.
2. *Junk values of `Δ`.* `Δ` is defined everywhere via `fderiv`, which is `0` at points of
   non-differentiability. In Theorem 1.1 it is only evaluated at `x ≠ 0`, where `u, v` are `C²`
   on an open neighbourhood, so `Δ u x` is the genuine Laplacian. In Corollary 1.2, `u, v` are
   `C²` on all of `ℝⁿ`.
3. *`C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)`.* Read as `ContDiffOn ℝ 2 u {0}ᶜ ∧ Continuous u` (twice continuously
   differentiable on the punctured space, continuous on the whole space). `ContDiffOn ℝ 2` on an
   open set is the same as classical `C²` there. `C²(ℝⁿ)` in Corollary 1.2 is `ContDiff ℝ 2`.
4. *`ℝⁿ`* is `EuclideanSpace ℝ (Fin n)`, so `|x|` is the Euclidean norm `‖x‖`.
5. *Powers.* `|x|^A`, `v^p`, `u^q` are real powers (`rpow`) because `A, p, q` are arbitrary
   reals. No junk: `|x|^A` is only used for `x ≠ 0` (positive base, so negative `A` is fine), and
   `u, v > 0` everywhere, so `v(x)^p`, `u(x)^q` have positive bases.
6. *Positivity.* The source asks `u(x) > 0`, `v(x) > 0` for all `x ∈ ℝⁿ` (including `x = 0`);
   kept literally. "Strictly positive" in Corollary 1.2 is read as `u > 0` and `v > 0`
   everywhere.
7. *Numeric hypotheses.* `n` is a natural number cast to `ℝ`; `n ≥ 2` (resp. `n ≥ 3`) as stated.
   Denominators `p+1`, `q+1`, `n` are positive under the hypotheses, so the divisions are genuine.
   For `n ≥ 2` the dimension is positive, so `{0}ᶜ` is a nonempty open set.
8. *"Satisfying (eq:system) at every `x ≠ 0`"* is a pointwise (classical) solution, not a weak or
   distributional one.
9. Corollary 1.2 is stated on its own, not derived from Theorem 1.1. (It is the special case
   `A = B = 0`: `n/(p+1) + n/(q+1) > n - 2` is the corollary's inequality multiplied by `n > 0`,
   `C²(ℝⁿ) ⊆ C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)`, and `|x|^0 = 1`, so the systems coincide away from `0`.)
-/
