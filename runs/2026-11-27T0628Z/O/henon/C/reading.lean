import Mathlib

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
