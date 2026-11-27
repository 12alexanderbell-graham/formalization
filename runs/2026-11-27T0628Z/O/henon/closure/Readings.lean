import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

open scoped Laplacian

namespace ReaderB

/-- Theorem 1.1: no positive `u, v ∈ C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)` solve the Hénon–Lane–Emden system
at every `x ≠ 0` under the subcriticality condition. -/
theorem reading_henon_theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q A B : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hsub : (n + A) / (p + 1) + (n + B) / (q + 1) > (n : ℝ) - 2) :
    ¬ ∃ u v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ 2 u {0}ᶜ ∧ ContDiffOn ℝ 2 v {0}ᶜ ∧ Continuous u ∧ Continuous v ∧
      (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
        -(Δ u x) = ‖x‖ ^ A * v x ^ p ∧ -(Δ v x) = ‖x‖ ^ B * u x ^ q) := sorry

/-- Corollary 1.2: unweighted Lane–Emden conjecture. -/
theorem reading_henon_corollary_1_2 (n : ℕ) (hn : 3 ≤ n) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hsub : 1 / (p + 1) + 1 / (q + 1) > ((n : ℝ) - 2) / n) :
    ¬ ∃ u v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 2 u ∧ ContDiff ℝ 2 v ∧ (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), -(Δ u x) = v x ^ p ∧ -(Δ v x) = u x ^ q) := sorry

/-
Ambiguities / choices.
* Laplacian: `Laplacian.laplacian` (notation `Δ`, scoped in `Laplacian`), the instance for
  functions `E → F` on a finite-dimensional real inner product space, here
  `E = EuclideanSpace ℝ (Fin n)`. It is defined from the global second derivative
  `iteratedFDeriv`; at x ≠ 0 it only depends on u near x, where u is C², so it agrees with the
  classical Laplacian. (Not `laplacianWithin`: unnecessary since {0}ᶜ is open.) Its value at 0
  is never used in Theorem 1.1 (equations only for x ≠ 0).
* C²(ℝⁿ∖{0}) ∩ C(ℝⁿ): `ContDiffOn ℝ 2 u {0}ᶜ ∧ Continuous u`. Positivity at all x including 0.
* Functions are real-valued on `EuclideanSpace ℝ (Fin n)`; n is a natural number, hypotheses
  n ≥ 2 (Thm) and n ≥ 3 (Cor) included. Subcriticality inequality has casts to ℝ.
* Powers `‖x‖^A`, `v^p`, `u^q` are `rpow`. Junk-free: at x ≠ 0 the base ‖x‖ > 0, and u, v > 0
  everywhere, so no rpow of negatives or 0^negative occurs. `-Δ u x` is `-(Δ u x)`.
* Corollary: C²(ℝⁿ) is `ContDiff ℝ 2` on the whole space, equations at every x (including 0),
  strictly positive; `(n-2)/n` with n ≥ 3 so no division by zero.
-/

end ReaderB

-- ===== reader C =====

/-!
Reading C of O30: "The subcritical Hénon–Lane–Emden conjecture" (only the excerpt
`henon/sources/introduction_lines1-68.tex` was read).
-/

open Filter Topology

namespace ReaderC

/-- The Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Theorem 1.1. Let `n ≥ 2`, `p,q > 0`, `A,B ∈ ℝ`, with
`(n+A)/(p+1) + (n+B)/(q+1) > n-2`. Then there are no `u, v ∈ C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)` with
`u(x) > 0`, `v(x) > 0` for all `x ∈ ℝⁿ`, satisfying the Hénon–Lane–Emden system
`-Δu = |x|^A v^p`, `-Δv = |x|^B u^q` at every `x ≠ 0`. -/
theorem reading_henon_thm11 (n : ℕ) (hn : 2 ≤ n) (p q A B : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hsub : ((n : ℝ) + A) / (p + 1) + ((n : ℝ) + B) / (q + 1) > (n : ℝ) - 2) :
    ¬ ∃ u v : Rn n → ℝ,
      ContDiffOn ℝ 2 u {0}ᶜ ∧ Continuous u ∧
      ContDiffOn ℝ 2 v {0}ᶜ ∧ Continuous v ∧
      (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      ∀ x : Rn n, x ≠ 0 →
        -Laplacian.laplacian u x = ‖x‖ ^ A * (v x) ^ p ∧
        -Laplacian.laplacian v x = ‖x‖ ^ B * (u x) ^ q := by
  sorry

/-- Corollary 1.2 (unweighted Lane–Emden). For `n ≥ 3` and `p,q > 0` with
`1/(p+1) + 1/(q+1) > (n-2)/n`, there is no strictly positive `C²(ℝⁿ)` solution of
`-Δu = v^p`, `-Δv = u^q` in `ℝⁿ`. -/
theorem reading_henon_cor12 (n : ℕ) (hn : 3 ≤ n) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hsub : 1 / (p + 1) + 1 / (q + 1) > ((n : ℝ) - 2) / n) :
    ¬ ∃ u v : Rn n → ℝ,
      ContDiff ℝ 2 u ∧ ContDiff ℝ 2 v ∧
      (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      ∀ x : Rn n,
        -Laplacian.laplacian u x = (v x) ^ p ∧
        -Laplacian.laplacian v x = (u x) ^ q := by
  sorry

end ReaderC

/-
Ambiguities and choices (Reader C, O30):

1. Laplacian: `Laplacian.laplacian` (the class `Laplacian` in
   `Mathlib/Analysis/Distribution/DerivNotation.lean`), whose instance on functions
   `E → F` for an inner product space `E` is `InnerProductSpace.instLaplacian`, defined as
   the second derivative contracted with the canonical covariant tensor, i.e. the usual
   `Σᵢ ∂ᵢ² u` for an orthonormal basis. This is the Laplacian on ℝⁿ with the standard
   Euclidean inner product. `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, whose inner product is the
   standard one, so the choice is the literal one. The Laplacian is a pointwise value
   defined via the derivatives at `x`; since `u` is C² on the open set `ℝⁿ∖{0}`, the values
   at `x ≠ 0` agree with the classical ones.
2. Regularity: `C²(ℝⁿ∖{0}) ∩ C(ℝⁿ)` is read as
   `ContDiffOn ℝ 2 u {0}ᶜ ∧ Continuous u`. `ContDiffOn ℝ 2` on the open set `{0}ᶜ` is the
   C² condition there (the same as `C²` on the open set, not just a one-sided
   or within-set condition). The two conditions are kept as separate conjuncts, as in the
   excerpt. `u` is not required to be C² at the origin, matching the excerpt.
3. Positivity: `u(x) > 0` and `v(x) > 0` for all `x ∈ ℝⁿ`, including `x = 0` (the excerpt
   says `x ∈ ℝⁿ`).
4. Weights and powers: `|x|^A` is `‖x‖ ^ A` with `Real.rpow` (A real). Since the equations
   are only asserted at `x ≠ 0`, `‖x‖ > 0` there, so no rpow-of-zero junk enters.
   `v^p`, `u^q` are `Real.rpow`; positivity of `u,v` makes them the genuine powers.
5. Dimension and parameters: `n ≥ 2` (Theorem), `n ≥ 3` (Corollary), `n` cast to `ℝ` in the
   exponent condition. `p,q > 0` and `A,B ∈ ℝ` as in the excerpt. The excerpt's hypothesis
   `(n+A)/(p+1) + (n+B)/(q+1) > n-2` is written literally with real division; `p+1 > 0`
   so no division-by-zero junk arises.
6. "There are no functions u, v ..." is formalized as `¬ ∃ u v, ...`, with the system holding
   "at every x ≠ 0" as the excerpt says.
7. Corollary 1.2: `C²(ℝⁿ)` is `ContDiff ℝ 2` on all of ℝⁿ, and the system is required at
   every `x ∈ ℝⁿ` (with `|x|^0 = 1` absorbed, the corollary's system has no weight, so the
   equation is `-Δu = v^p`, `-Δv = u^q` at all points including 0). The excerpt says
   "strictly positive", read as `∀ x, 0 < u x` and `∀ x, 0 < v x`. Positive reals with
   `rpow` are the genuine powers.
8. Corollary 1.2 is stated as its own theorem, with the exponent condition
   `1/(p+1) + 1/(q+1) > (n-2)/n` literally. It is not derived from Theorem 1.1 inside
   Lean (the excerpt presents it as the unweighted case A = B = 0).
9. The bibliography, the history, and the description of the conjecture in the excerpt
   are not claims to be formalized.
-/
