import Mathlib

/-!
Blind reading (reader A) of the introduction of "Tingley's sphere-isometry problem":
Theorem 1.1.
-/

namespace ReaderA

open Metric

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- For `x ≠ 0`, `x / ‖x‖` lies on the unit sphere `S_X`. -/
theorem inv_norm_smul_mem_sphere {x : X} (hx : x ≠ 0) :
    (‖x‖⁻¹ : ℝ) • x ∈ sphere (0 : X) 1 :=
  mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)

open Classical in
/-- The radial map `T(0) = 0`, `T(x) = ‖x‖ f(x / ‖x‖)` for `x ≠ 0`. -/
noncomputable def radialMap (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (x : X) : Y :=
  if hx : x = 0 then 0 else ‖x‖ • (f ⟨(‖x‖⁻¹ : ℝ) • x, inv_norm_smul_mem_sphere hx⟩ : Y)

/-- Theorem 1.1.  `X, Y` nonzero real Banach spaces, `f : S_X → S_Y` a surjective isometry
(for the metric inherited from `X`, `Y`).  Then `T` is a surjective real-linear isometry, and it
is the unique linear extension of `f`: it extends `f`, and every real-linear map `X → Y`
extending `f` equals `T`. -/
theorem reading_thm_1_1 [CompleteSpace X] [CompleteSpace Y] [Nontrivial X] [Nontrivial Y]
    (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (hf : Isometry f)
    (hfs : Function.Surjective f) :
    (IsLinearMap ℝ (radialMap f) ∧ Isometry (radialMap f) ∧
        Function.Surjective (radialMap f)) ∧
      (∀ x : sphere (0 : X) 1, radialMap f (x : X) = (f x : Y)) ∧
      (∀ S : X →ₗ[ℝ] Y, (∀ x : sphere (0 : X) 1, S (x : X) = (f x : Y)) →
        ⇑S = radialMap f) := by
  sorry

end ReaderA

/-!
## Ambiguities and choices (reader A)

* "real Banach space": `NormedAddCommGroup` + `NormedSpace ℝ` + `CompleteSpace`.  "nonzero":
  `Nontrivial` (the space is not `{0}`), for both `X` and `Y`.
* `S_X = {x : ‖x‖ = 1}` is `Metric.sphere (0 : X) 1` as a subtype; its metric is the subtype
  metric, i.e. the distance inherited from `X`, as the text says.  "isometry" is Mathlib's
  `Isometry` (distance-preserving; for maps of metric spaces this is the same as preserving
  `edist`).  "surjective" is `Function.Surjective` onto `S_Y`.
* `T`: defined by cases exactly as displayed, `x / ‖x‖` written `‖x‖⁻¹ • x`.  Junk avoidance: the
  `x ≠ 0` branch carries the proof `x ≠ 0`, so `‖x‖⁻¹` is never `0⁻¹`; the `x = 0` case is the
  explicit `T(0) = 0`.
* "surjective real-linear isometry" is the conjunction `IsLinearMap ℝ T ∧ Isometry T ∧
  Surjective T` (rather than packaging as `X ≃ₗᵢ[ℝ] Y`, which would require T to be given as a
  structure; the conjunction is equivalent).
* "It is the unique linear extension of f": read as two claims: (i) `T` extends `f`
  (`T x = f x` for `x ∈ S_X`; true by construction), and (ii) every real-linear map `S : X → Y`
  with `S x = f x` on `S_X` equals `T`.  "linear" is read as real-linear (the paper says only
  real linearity is asserted, also for complex spaces).  Uniqueness is among all real-linear
  maps, not only among isometries or continuous ones.
* The hypotheses `Isometry f`, surjectivity, completeness and nontriviality are all kept even
  where (for (i)) they are not needed.
-/
