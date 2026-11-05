import Mathlib
import Work.Math.LEExistsLeft

/-!
# Lane–Emden n = 3: existence of a solution meeting every hypothesis of `laneEmden3_constants`

The singular piece on [0, 1/2] (`Work.Math.LEExistsLeft.exists_left`, Banach fixed point of the
Volterra map) is continued on [1/2, 7] by Picard–Lindelöf (`Work.Math.LEExistsRight.exists_right`)
from its values at 1/2 and glued: at 1/2 the one-sided derivatives of both pieces agree, so the
derivative within [0, 7] exists (`HasDerivWithinAt.union`).
-/

namespace Work.Math.LEExists
open Set Filter Topology

/-- Gluing two one-sided derivatives at 1/2. -/
theorem glue {fL fR d : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 7) (heq : fL (1 / 2) = fR (1 / 2))
    (hL : x ≤ 1 / 2 → HasDerivWithinAt fL (d x) (Icc 0 (1 / 2)) x)
    (hR : 1 / 2 ≤ x → HasDerivWithinAt fR (d x) (Icc (1 / 2) 7) x) :
    HasDerivWithinAt (fun y => if y ≤ 1 / 2 then fL y else fR y) (d x) (Icc 0 7) x := by
  set F : ℝ → ℝ := fun y => if y ≤ 1 / 2 then fL y else fR y with hF
  have eL : EqOn F fL (Icc 0 (1 / 2)) := fun y hy => by rw [hF]; exact if_pos hy.2
  have eR : EqOn F fR (Icc (1 / 2) 7) := fun y hy => by
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; rw [hF]; exact (if_pos le_rfl).trans heq
    · rw [hF]; exact if_neg (not_le.2 h)
  have hL' : x ≤ 1 / 2 → HasDerivWithinAt F (d x) (Icc 0 (1 / 2)) x := fun h =>
    (hL h).congr eL (eL ⟨hx.1, h⟩)
  have hR' : 1 / 2 ≤ x → HasDerivWithinAt F (d x) (Icc (1 / 2) 7) x := fun h =>
    (hR h).congr eR (eR ⟨h, hx.2⟩)
  rcases lt_trichotomy x (1 / 2) with h | h | h
  · refine (hL' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio (1 / 2), isOpen_Iio, h, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩)
  · have hu : Icc (0 : ℝ) 7 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 7 :=
      (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
    rw [hu]
    exact (hL' h.le).union (hR' h.ge)
  · refine (hR' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi (1 / 2), isOpen_Ioi, h, fun y hy => ⟨le_of_lt hy.1, hy.2.2⟩⟩)

/-- Existence: a θ, φ on [0, 7] satisfying every hypothesis of
`Work.Math.LaneEmden.laneEmden3_constants` (θ' = φ within [0, 7], φ continuous at 0,
φ' = −(2/ξ)φ − θ³ on (0, 7], θ(0) = 1). -/
theorem exists_solution : ∃ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ) ∧
    ContinuousWithinAt φ (Icc 0 7) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ) ∧
    θ 0 = 1 := by
  obtain ⟨θL, φL, h0, hcφ, hθb, hφb, hdθ, hdφ⟩ := Work.Math.LEExistsLeft.exists_left
  obtain ⟨θR, φR, hθR, hφR, hR⟩ := Work.Math.LEExistsRight.exists_right _ _ hθb hφb
  set θ : ℝ → ℝ := fun y => if y ≤ 1 / 2 then θL y else θR y with hθ
  set φ : ℝ → ℝ := fun y => if y ≤ 1 / 2 then φL y else φR y with hφ
  have θl : ∀ y, y ≤ 1 / 2 → θ y = θL y := fun y h => by rw [hθ]; exact if_pos h
  have φl : ∀ y, y ≤ 1 / 2 → φ y = φL y := fun y h => by rw [hφ]; exact if_pos h
  have θr : ∀ y, 1 / 2 ≤ y → θ y = θR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hθ]; exact (if_pos le_rfl).trans hθR.symm
    · rw [hθ]; exact if_neg (not_le.2 h)
  have φr : ∀ y, 1 / 2 ≤ y → φ y = φR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hφ]; exact (if_pos le_rfl).trans hφR.symm
    · rw [hφ]; exact if_neg (not_le.2 h)
  refine ⟨θ, φ, fun ξ hξ => ?_, ?_, fun ξ hξ => ?_, (θl 0 (by norm_num)).trans h0⟩
  · exact glue hξ hθR.symm
      (fun h => by rw [φl ξ h]; exact hdθ ξ ⟨hξ.1, h⟩)
      (fun h => by rw [φr ξ h]; exact (hR ξ ⟨h, hξ.2⟩).1)
  · have e : φ =ᶠ[𝓝[Icc 0 7] 0] φL := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
        with y hy using φl y (le_of_lt hy)
    exact (hcφ.continuousWithinAt).congr_of_eventuallyEq e (φl 0 (by norm_num))
  · have hξ' : ξ ∈ Icc (0 : ℝ) 7 := Ioc_subset_Icc_self hξ
    exact glue (d := fun y => -(2 / y * φ y) - θ y ^ 3) hξ' hφR.symm
      (fun h => by
        simp only [φl ξ h, θl ξ h]; exact hdφ ξ ⟨hξ.1, h⟩)
      (fun h => by
        simp only [φr ξ h, θr ξ h]; exact (hR ξ ⟨h, hξ.2⟩).2)

end Work.Math.LEExists

#print axioms Work.Math.LEExists.exists_solution
