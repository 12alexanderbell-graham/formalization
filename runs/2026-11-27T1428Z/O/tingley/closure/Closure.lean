import Mathlib
import Readings.tingley
import ComparatorChallenges.TingleySphereIsometry

/-! # Target O, family O48 (Tingley's problem): closures (run 2026-11-27T1428Z).
Frozen statement `tingley_sphere_isometry_full` (unit sphere as the subtype `‖x‖ = 1`), taken with `type_of%`,
never retyped. The readers' spheres are `Metric.sphere 0 1`; a reader's `f` is transported to the frozen sphere
(the two subtypes carry the same points and the same distances), and the frozen `T` is shown equal to each
reader's radial map. Closed: every reader's Theorem 1.1 (3/3). -/

namespace TargetO.Tingley

open OAI.Tingley Metric

universe u v

variable {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- A reader's sphere map, transported to the frozen unit sphere. -/
def tr (f : sphere (0 : X) 1 → sphere (0 : Y) 1) : UnitSphere X → UnitSphere Y :=
  fun u => ⟨(f ⟨u.1, mem_sphere_zero_iff_norm.2 u.2⟩ : Y), mem_sphere_zero_iff_norm.1 (f _).2⟩

theorem tr_isometry {f : sphere (0 : X) 1 → sphere (0 : Y) 1} (hf : Isometry f) : Isometry (tr f) := by
  refine Isometry.of_dist_eq fun a b => ?_
  have := hf.dist_eq ⟨a.1, mem_sphere_zero_iff_norm.2 a.2⟩ ⟨b.1, mem_sphere_zero_iff_norm.2 b.2⟩
  simpa [tr, Subtype.dist_eq] using this

theorem tr_surj {f : sphere (0 : X) 1 → sphere (0 : Y) 1} (hs : Function.Surjective f) :
    Function.Surjective (tr f) := by
  intro w
  obtain ⟨u, hu⟩ := hs ⟨w.1, mem_sphere_zero_iff_norm.2 w.2⟩
  exact ⟨⟨u.1, mem_sphere_zero_iff_norm.1 u.2⟩, Subtype.ext (by simp [tr, hu])⟩

/-- The frozen theorem, specialised to a reader's `f`: a linear isometric equivalence extending `f`, equal to the
radial formula off zero, and the only linear extension. -/
theorem frozen_for [CompleteSpace X] [CompleteSpace Y] [Nontrivial X] [Nontrivial Y]
    (H : type_of% @tingley_sphere_isometry_full.{u, v})
    (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (hf : Isometry f) (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, (∀ u : sphere (0 : X) 1, T (u : X) = (f u : Y)) ∧ T 0 = 0 ∧
      (∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hx)⟩ : Y)) ∧
      Function.Surjective T ∧
      (∀ L : X →ₗ[ℝ] Y, (∀ u : sphere (0 : X) 1, L (u : X) = (f u : Y)) → L = T.toLinearEquiv.toLinearMap) := by
  obtain ⟨T, h1, h0, hr, hsT, hu⟩ := H (tr f) (tr_isometry hf) (tr_surj hs)
  refine ⟨T, fun u => h1 ⟨u.1, mem_sphere_zero_iff_norm.1 u.2⟩, h0, fun x hx => hr x hx, hsT,
    fun L hL => hu L fun u => hL ⟨u.1, mem_sphere_zero_iff_norm.2 u.2⟩⟩

theorem A_eq [CompleteSpace X] [CompleteSpace Y] [Nontrivial X] [Nontrivial Y]
    (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (T : X ≃ₗᵢ[ℝ] Y) (h0 : T 0 = 0)
    (hr : ∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hx)⟩ : Y)) :
    ⇑T = ReaderA.radialMap f := by
  funext x
  unfold ReaderA.radialMap
  split_ifs with hx
  · rw [hx, h0]
  · exact hr x hx

theorem A_thm [CompleteSpace X] [CompleteSpace Y] [Nontrivial X] [Nontrivial Y]
    (H : type_of% @tingley_sphere_isometry_full.{u, v}) :
    ∀ (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (hf : Isometry f) (hfs : Function.Surjective f),
      (IsLinearMap ℝ (ReaderA.radialMap f) ∧ Isometry (ReaderA.radialMap f) ∧
        Function.Surjective (ReaderA.radialMap f)) ∧
      (∀ x : sphere (0 : X) 1, ReaderA.radialMap f (x : X) = (f x : Y)) ∧
      (∀ S : X →ₗ[ℝ] Y, (∀ x : sphere (0 : X) 1, S (x : X) = (f x : Y)) → ⇑S = ReaderA.radialMap f) := by
  intro f hf hfs
  obtain ⟨T, h1, h0, hr, hsT, hu⟩ := frozen_for H f hf hfs
  have e := A_eq f T h0 hr
  rw [← e]
  exact ⟨⟨T.toLinearEquiv.toLinearMap.isLinear, T.isometry, hsT⟩, h1, fun S hS => by rw [hu S hS]; rfl⟩

theorem B_thm (H : type_of% @tingley_sphere_isometry_full.{u, v}) [CompleteSpace X] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y] (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (hf : Isometry f)
    (hs : Function.Surjective f) :
    (∃ T : X →ₗᵢ[ℝ] Y, ⇑T = ReaderB.radialExt f ∧ Function.Surjective T ∧
        (∀ x : sphere (0 : X) 1, T x = f x)) ∧
    (∀ T' : X →ₗ[ℝ] Y, (∀ x : sphere (0 : X) 1, T' x = (f x : Y)) → ⇑T' = ReaderB.radialExt f) := by
  obtain ⟨T, h1, h0, hr, hsT, hu⟩ := frozen_for H f hf hs
  have e : ⇑T = ReaderB.radialExt f := by
    funext x
    unfold ReaderB.radialExt
    split_ifs with hx
    · rw [hx, h0]
    · exact hr x hx
  refine ⟨⟨T.toLinearIsometry, e, hsT, h1⟩, fun T' hT' => ?_⟩
  rw [hu T' hT', ← e]; rfl

theorem C_thm (H : type_of% @tingley_sphere_isometry_full.{u, v}) [CompleteSpace X] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y] (f : sphere (0 : X) 1 → sphere (0 : Y) 1) (hf : Isometry f)
    (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, (∀ x : X, T x = ReaderC.radialMap f x) ∧
      (∀ u : sphere (0 : X) 1, T (u : X) = (f u : Y)) ∧
      (∀ S : X →ₗ[ℝ] Y, (∀ u : sphere (0 : X) 1, S (u : X) = (f u : Y)) → ∀ x : X, S x = T x) := by
  obtain ⟨T, h1, h0, hr, hsT, hu⟩ := frozen_for H f hf hs
  refine ⟨T, fun x => ?_, h1, fun S hS x => by rw [hu S hS]; rfl⟩
  unfold ReaderC.radialMap
  split_ifs with hx
  · rw [hx, h0]
  · exact hr x hx

/-! The readers' theorems themselves, from the frozen one. -/

theorem A_final (H : type_of% @tingley_sphere_isometry_full.{u, v}) : type_of% @ReaderA.reading_thm_1_1.{u, v} := by
  intro X' Y' _ _ _ _ _ _ _ _ f hf hfs
  exact A_thm H f hf hfs

theorem B_final (H : type_of% @tingley_sphere_isometry_full.{u, v}) : type_of% @ReaderB.reading_thm_1_1.{u, v} := by
  intro X' Y' _ _ _ _ _ _ _ _ f hf hfs
  exact B_thm H f hf hfs

theorem C_final (H : type_of% @tingley_sphere_isometry_full.{u, v}) : type_of% @ReaderC.reading_theorem_1_1.{u, v} := by
  intro X' Y' _ _ _ _ _ _ _ _ f hf hfs
  exact C_thm H f hf hfs

end TargetO.Tingley

#print axioms TargetO.Tingley.A_final
#print axioms TargetO.Tingley.B_final
#print axioms TargetO.Tingley.C_final
