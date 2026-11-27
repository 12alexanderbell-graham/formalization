import Mathlib
import Readings.Plane5
import ComparatorChallenges.EuclideanFiveColor

/-! # Target O, family O4 (the plane is not five-colorable): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped; it lives on `ℂ` with `‖p - q‖ = 1`, the readers on
`EuclideanSpace ℝ (Fin 2)`: the two are related by the linear isometry `Complex.orthonormalBasisOneI.repr`.
Not closed: every reading that includes χ(ℝ²) ≤ 7 (Isbell's seven-coloring, which the manuscript cites and
does not prove; no frozen statement carries it). -/

namespace TargetO.Plane5

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def e : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

theorem e_unit {p q : ℂ} : ‖e p - e q‖ = ‖p - q‖ := by
  rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem e_symm_unit {x y : Plane} : ‖e.symm x - e.symm y‖ = ‖x - y‖ := by
  rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- The frozen statement, transported to the Euclidean plane, for any colour type injecting into `Fin 5`. -/
theorem no_coloring_of_inj {α : Type} (f : α → Fin 5) (hf : Function.Injective f)
    (h : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring)) :
    ¬ ∃ c : Plane → α, ∀ x y : Plane, ‖x - y‖ = 1 → c x ≠ c y := by
  rintro ⟨c, hc⟩
  apply h
  refine ⟨fun p => f (c (e p)), fun p q hpq hEq => ?_⟩
  exact hc (e p) (e q) (by rw [e_unit]; exact hpq) (hf hEq)

theorem B_no_five : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring) ↔
    (type_of% @ReaderB.reading_plane_not_five_colorable) := by
  constructor
  · rintro h ⟨c, hc⟩
    exact no_coloring_of_inj id Function.injective_id h ⟨c, fun x y hxy => hc x y (by rwa [dist_eq_norm])⟩
  · rintro h ⟨c, hc⟩
    exact h ⟨fun x => c (e.symm x), fun x y hxy => hc _ _ (by rw [e_symm_unit, ← dist_eq_norm]; exact hxy)⟩

theorem C_no_five : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring) ↔
    (type_of% @ReaderC.reading_no_proper_five_coloring) := by
  constructor
  · rintro h ⟨c, hc⟩
    exact no_coloring_of_inj id Function.injective_id h ⟨c, fun x y hxy => hc x y (by rwa [dist_eq_norm])⟩
  · rintro h ⟨c, hc⟩
    exact h ⟨fun x => c (e.symm x), fun x y hxy => hc _ _ (by rw [e_symm_unit, ← dist_eq_norm]; exact hxy)⟩

theorem C_chi_lower : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring) →
    (type_of% @ReaderC.reading_chi_lower) := by
  intro h k hk ⟨c, hc⟩
  exact no_coloring_of_inj (Fin.castLE (by omega)) (Fin.castLE_injective _) h
    ⟨c, fun x y hxy => hc x y (by rwa [dist_eq_norm])⟩

theorem A_no_five : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring) ↔
    (type_of% @ReaderA.Plane5ReadingA.reading_thm_1_1_no_five_coloring) := by
  constructor
  · rintro h ⟨c, hc⟩
    refine no_coloring_of_inj (fun x : ReaderA.Plane5ReadingA.Colors 5 =>
      (⟨x.1 - 1, by have := x.2.2; omega⟩ : Fin 5)) ?_ h ⟨c, hc⟩
    intro x y hxy
    have h1 := x.2.1; have h2 := y.2.1
    simp only [Fin.mk.injEq] at hxy
    exact Subtype.ext (by omega)
  · rintro h ⟨c, hc⟩
    apply h
    refine ⟨fun x => (⟨(c (e.symm x)).1 + 1, by constructor <;> omega⟩ :
      ReaderA.Plane5ReadingA.Colors 5), fun x y hxy hEq => ?_⟩
    apply hc (e.symm x) (e.symm y) (by rw [e_symm_unit]; exact hxy)
    have h3 := congrArg Subtype.val hEq
    simp only at h3
    exact Fin.ext (by omega)

end TargetO.Plane5

#print axioms TargetO.Plane5.B_no_five
#print axioms TargetO.Plane5.C_no_five
#print axioms TargetO.Plane5.C_chi_lower
#print axioms TargetO.Plane5.A_no_five
