import Mathlib

open Metric

namespace ReaderC

open Classical in
/-- The radial map `T(0) = 0`, `T(x) = ‖x‖ f(x/‖x‖)` for `x ≠ 0`, built from a surjective
isometry `f` between unit spheres. The sphere point `‖x‖⁻¹ • x` lies on the unit sphere
by `norm_smul_inv_norm`. (`open Classical` supplies decidability of `x = 0`.) -/
noncomputable def radialMap {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (x : X) : Y :=
  if h : x = 0 then 0
  else ‖x‖ • ((f ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm]
      exact norm_smul_inv_norm h⟩ : sphere (0 : Y) 1) : Y)

/-- Theorem 1.1 (Tingley's problem, affirmative). Nonzero real Banach spaces `X`, `Y`; a
surjective isometry `f` between unit spheres extends to a surjective real-linear isometry
`T`, `T` is given by the radial formula, and `T` is the unique linear extension of `f`. -/
theorem reading_theorem_1_1 {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [Nontrivial Y]
    (f : sphere (0 : X) 1 → sphere (0 : Y) 1)
    (hf : Isometry f) (hsurj : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y,
      (∀ x : X, T x = radialMap f x) ∧
      (∀ u : sphere (0 : X) 1, T (u : X) = (f u : Y)) ∧
      (∀ S : X →ₗ[ℝ] Y, (∀ u : sphere (0 : X) 1, S (u : X) = (f u : Y)) →
        ∀ x : X, S x = T x) := sorry

/-!
## Ambiguities and choices

1. "Nonzero real Banach space": real normed space (`NormedSpace ℝ`), complete
   (`CompleteSpace`), and nonzero (`Nontrivial`). Nonzero is `Nontrivial` (some `x ≠ 0`).
   Complex spaces viewed as real spaces are covered automatically, since the `ℝ`-module
   structure is used; complex linearity is not asserted, as in the text.
2. Unit spheres `S_X`: `Metric.sphere (0 : X) 1` as a subtype of `X`, with the inherited
   metric. A surjective isometry `f : S_X → S_Y` is `Isometry f` plus `Function.Surjective f`
   on the subtypes. Thus `f` maps sphere points to sphere points, as the text requires.
3. "Surjective real-linear isometry": `X ≃ₗᵢ[ℝ] Y` (a linear isometric equivalence). This
   is a bijective real-linear isometry, and it is the strongest form of "surjective
   real-linear isometry" Mathlib provides. Injectivity and surjectivity come from
   `LinearIsometryEquiv`.
4. The formula `T(0)=0`, `T(x)=‖x‖ f(x/‖x‖)`: `radialMap f` implements it. The conjunct
   `∀ x, T x = radialMap f x` pins `T` to the text's map. The `if h : x = 0` clause is
   exactly the text's case split, so no division by `0` occurs: `‖x‖⁻¹` is used only when
   `x ≠ 0` (the `h` proof is in scope), so `x/‖x‖` is never computed at `x = 0`.
   The inner sphere point `‖x‖⁻¹ • x` is in the sphere by `norm_smul_inv_norm`, so the
   subtype witness is genuine (this is a proof, not a junk value).
5. "T is the unique linear extension of f": `f` is extended by `T` on the sphere
   (`∀ u, T u = f u`, with `f u : Y` coerced), and uniqueness is among all real-linear maps
   `S : X →ₗ[ℝ] Y` with `S u = f u` on the sphere. Uniqueness is stated as "every such
   `S` agrees with `T` everywhere on `X`", which is the literal meaning of uniqueness.
6. No `sSup`, `ℕ`-subtraction, `ℝ≥0∞` volumes, or real powers occur in this file, so none of
   the junk-value cases arise.
7. The `Nontrivial` instance on `Y` is needed for the statement to be the text's (nonzero
   spaces). `hf` and `hsurj` together are the text's "surjective isometry".
-/

end ReaderC
