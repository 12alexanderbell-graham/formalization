import Mathlib

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
