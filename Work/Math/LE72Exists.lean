import Work.Math.LE72ExistsLeft
import Work.Math.LE72ExistsRight

/-!
# Lane–Emden index seven halves: existence of a solution meeting every hypothesis of `laneEmden72_constants`

The singular piece (`Work.Math.LE72ExistsLeft.exists_left`, Banach fixed point of the Volterra
map) is continued by Picard–Lindelöf (`Work.Math.LE72ExistsRight.exists_right`) from its values at
the junction and glued there (the index-three construction `Checked.Math.LEExists` with the power
seven halves, range [0, 10]); the power is Mathlib's real power through
`Work.Math.LE72Cell.rpow72_eq`. Run 2026-11-19T2228Z (from the index five halves module of run 2026-11-19T1628Z).
-/

namespace Work.Math.LE72Exists
open Set Filter Topology

/-- Gluing two one-sided derivatives at 1/2. -/
theorem glue {fL fR d : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 10) (heq : fL (1 / 2) = fR (1 / 2))
    (hL : x ≤ 1 / 2 → HasDerivWithinAt fL (d x) (Icc 0 (1 / 2)) x)
    (hR : 1 / 2 ≤ x → HasDerivWithinAt fR (d x) (Icc (1 / 2) 10) x) :
    HasDerivWithinAt (fun y => if y ≤ 1 / 2 then fL y else fR y) (d x) (Icc 0 10) x := by
  set F : ℝ → ℝ := fun y => if y ≤ 1 / 2 then fL y else fR y with hF
  have eL : EqOn F fL (Icc 0 (1 / 2)) := fun y hy => by rw [hF]; exact if_pos hy.2
  have eR : EqOn F fR (Icc (1 / 2) 10) := fun y hy => by
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; rw [hF]; exact (if_pos le_rfl).trans heq
    · rw [hF]; exact if_neg (not_le.2 h)
  have hL' : x ≤ 1 / 2 → HasDerivWithinAt F (d x) (Icc 0 (1 / 2)) x := fun h =>
    (hL h).congr eL (eL ⟨hx.1, h⟩)
  have hR' : 1 / 2 ≤ x → HasDerivWithinAt F (d x) (Icc (1 / 2) 10) x := fun h =>
    (hR h).congr eR (eR ⟨h, hx.2⟩)
  rcases lt_trichotomy x (1 / 2) with h | h | h
  · refine (hL' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio (1 / 2), isOpen_Iio, h, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩)
  · have hu : Icc (0 : ℝ) 10 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 10 :=
      (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
    rw [hu]
    exact (hL' h.le).union (hR' h.ge)
  · refine (hR' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi (1 / 2), isOpen_Ioi, h, fun y hy => ⟨le_of_lt hy.1, hy.2.2⟩⟩)

/-- There exist θ, φ with θ differentiable within [0, 10] with derivative φ, φ continuous at 0,
φ' = −(2/ξ)φ − θ ^ (7/2) on (0, 10] and θ(0) = 1: the hypotheses of the Lane–Emden headline
`Work.Math.LaneEmden72.laneEmden72_constants` are satisfied together (a solution regular at the centre
exists). -/
theorem exists_solution : ∃ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 10, HasDerivWithinAt θ (φ ξ) (Icc 0 10) ξ) ∧
    ContinuousWithinAt φ (Icc 0 10) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) 10, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((7 : ℝ) / 2)) (Icc 0 10) ξ) ∧
    θ 0 = 1 := by
  obtain ⟨θL, φL, h0, hcφ, hθb, hφb, hdθ, hdφ⟩ := Work.Math.LE72ExistsLeft.exists_left
  obtain ⟨θR, φR, hθR, hφR, hR⟩ := Work.Math.LE72ExistsRight.exists_right _ _ hθb hφb
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
  · have e : φ =ᶠ[𝓝[Icc 0 10] 0] φL := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
        with y hy using φl y (le_of_lt hy)
    exact (hcφ.continuousWithinAt).congr_of_eventuallyEq e (φl 0 (by norm_num))
  · have hξ' : ξ ∈ Icc (0 : ℝ) 10 := Ioc_subset_Icc_self hξ
    exact glue (d := fun y => -(2 / y * φ y) - θ y ^ ((7 : ℝ) / 2)) hξ' hφR.symm
      (fun h => by
        simp only [φl ξ h, θl ξ h, Work.Math.LE72Cell.rpow72_eq]; exact hdφ ξ ⟨hξ.1, h⟩)
      (fun h => by
        simp only [φr ξ h, θr ξ h, Work.Math.LE72Cell.rpow72_eq]; exact (hR ξ ⟨h, hξ.2⟩).2)

end Work.Math.LE72Exists

