import Mathlib

/-! # Target O, family tingley: the three blind readings of run 2026-11-27T1428Z (brief 7bfe069), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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


open Classical

namespace ReaderB

/-- The radial candidate `T(0)=0`, `T(x) = ‖x‖ • f (x/‖x‖)`. -/
noncomputable def radialExt {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Metric.sphere (0 : X) 1 → Metric.sphere (0 : Y) 1) (x : X) : Y :=
  if h : x = 0 then 0
  else ‖x‖ • ((f ⟨‖x‖⁻¹ • x, by
    simp [norm_smul, norm_ne_zero_iff.mpr h]⟩ : Metric.sphere (0 : Y) 1) : Y)

/-- Theorem 1.1 (Tingley's problem). -/
theorem reading_thm_1_1 (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [Nontrivial Y]
    (f : Metric.sphere (0 : X) 1 → Metric.sphere (0 : Y) 1)
    (hf : Isometry f) (hs : Function.Surjective f) :
    (∃ T : X →ₗᵢ[ℝ] Y, ⇑T = radialExt f ∧ Function.Surjective T ∧
        (∀ x : Metric.sphere (0 : X) 1, T x = f x)) ∧
    (∀ T' : X →ₗ[ℝ] Y, (∀ x : Metric.sphere (0 : X) 1, T' x = (f x : Y)) →
        ⇑T' = radialExt f) := by
  sorry

/-
Ambiguities and choices.
* "Nonzero real Banach space": `NormedAddCommGroup`, `NormedSpace ℝ`, `CompleteSpace`, `Nontrivial`.
* Unit sphere S_X = `Metric.sphere 0 1` as a subtype with the induced metric; "isometry" = Mathlib `Isometry`
  (distance preserving, not merely injective); surjectivity as stated.
* T defined by `radialExt`, using `dite` on `x = 0` (so the x/0 junk case is excluded: the sphere membership
  of x/‖x‖ is proven inside the definition under x ≠ 0).
* "T is a surjective real-linear isometry": `T : X →ₗᵢ[ℝ] Y` (linear isometry) with `⇑T = radialExt f`
  and surjectivity.
* "It is the unique linear extension of f": (a) T extends f on the sphere, (b) any real-linear map T' extending
  f has `⇑T' = radialExt f` (= ⇑T). Uniqueness is over all real-linear maps, not only isometries or continuous.
* The definitions of S_X, f, T are universe-polymorphic in X, Y separately.
-/

end ReaderB


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
