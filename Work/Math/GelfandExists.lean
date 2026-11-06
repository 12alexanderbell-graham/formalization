import Mathlib
import Work.Math.GExistsLeft
import Work.Math.GExistsRight

/-!
# Gelfand problem in the 3-D ball: existence of a solution meeting every hypothesis of the
# headline `Work.Math.Gelfand.gelfand_ball_critical`

Frozen before proof (annex 40.1), run 2026-11-06T1228Z. For every S ≥ 1/2 there are w, φ with
w differentiable within [0, S] with derivative φ, φ continuous at 0, φ' = −(2/s)φ − e^w on (0, S]
and w(0) = 0 (the regular solution of the isothermal Emden–Chandrasekhar equation exists on
[0, S]). Planned route: the Lane–Emden existence route (`Work/Math/LEExists*.lean`) with θ³
replaced by a clamped exponential; on [1/2, S] the clamps stay inactive because s²φ is
decreasing (so w ≤ 0) and bounded below.
-/

namespace Work.Math.GelfandExists
open Set Filter Topology

/-- Gluing two one-sided derivatives at 1/2. -/
theorem glue {S : ℝ} {fL fR d : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) S)
    (hS : 1 / 2 ≤ S) (heq : fL (1 / 2) = fR (1 / 2))
    (hL : x ≤ 1 / 2 → HasDerivWithinAt fL (d x) (Icc 0 (1 / 2)) x)
    (hR : 1 / 2 ≤ x → HasDerivWithinAt fR (d x) (Icc (1 / 2) S) x) :
    HasDerivWithinAt (fun y => if y ≤ 1 / 2 then fL y else fR y) (d x) (Icc 0 S) x := by
  set F : ℝ → ℝ := fun y => if y ≤ 1 / 2 then fL y else fR y with hF
  have eL : EqOn F fL (Icc 0 (1 / 2)) := fun y hy => by rw [hF]; exact if_pos hy.2
  have eR : EqOn F fR (Icc (1 / 2) S) := fun y hy => by
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; rw [hF]; exact (if_pos le_rfl).trans heq
    · rw [hF]; exact if_neg (not_le.2 h)
  have hL' : x ≤ 1 / 2 → HasDerivWithinAt F (d x) (Icc 0 (1 / 2)) x := fun h =>
    (hL h).congr eL (eL ⟨hx.1, h⟩)
  have hR' : 1 / 2 ≤ x → HasDerivWithinAt F (d x) (Icc (1 / 2) S) x := fun h =>
    (hR h).congr eR (eR ⟨h, hx.2⟩)
  rcases lt_trichotomy x (1 / 2) with h | h | h
  · refine (hL' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio (1 / 2), isOpen_Iio, h, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩)
  · have hu : Icc (0 : ℝ) S = Icc 0 (1 / 2) ∪ Icc (1 / 2) S :=
      (Icc_union_Icc_eq_Icc (by norm_num) hS).symm
    rw [hu]
    exact (hL' h.le).union (hR' h.ge)
  · refine (hR' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi (1 / 2), isOpen_Ioi, h, fun y hy => ⟨le_of_lt hy.1, hy.2.2⟩⟩)

/-- For every S ≥ 1/2 there exist w, φ with w differentiable within [0, S] with derivative φ, φ
continuous at 0, φ' = −(2/s)φ − e^w on (0, S] and w(0) = 0: the hypotheses of the Gelfand
headline are satisfied together. -/
theorem exists_solution (S : ℝ) (hS : 1 / 2 ≤ S) : ∃ w φ : ℝ → ℝ,
    (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s) ∧
    ContinuousWithinAt φ (Icc 0 S) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s) ∧
    w 0 = 0 := by
  obtain ⟨wL, φL, h0, hcφ, hwb, hφb, hφb', hdw, hdφ⟩ := Work.Math.GExistsLeft.exists_left
  obtain ⟨wR, φR, hwR, hφR, hR⟩ := Work.Math.GExistsRight.exists_right S _ _ hS hwb hφb hφb'
  set w : ℝ → ℝ := fun y => if y ≤ 1 / 2 then wL y else wR y with hw
  set φ : ℝ → ℝ := fun y => if y ≤ 1 / 2 then φL y else φR y with hφ
  have wl : ∀ y, y ≤ 1 / 2 → w y = wL y := fun y h => by rw [hw]; exact if_pos h
  have φl : ∀ y, y ≤ 1 / 2 → φ y = φL y := fun y h => by rw [hφ]; exact if_pos h
  have wr : ∀ y, 1 / 2 ≤ y → w y = wR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hw]; exact (if_pos le_rfl).trans hwR.symm
    · rw [hw]; exact if_neg (not_le.2 h)
  have φr : ∀ y, 1 / 2 ≤ y → φ y = φR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hφ]; exact (if_pos le_rfl).trans hφR.symm
    · rw [hφ]; exact if_neg (not_le.2 h)
  refine ⟨w, φ, fun s hs => ?_, ?_, fun s hs => ?_, (wl 0 (by norm_num)).trans h0⟩
  · exact glue hs hS hwR.symm
      (fun h => by rw [φl s h]; exact hdw s ⟨hs.1, h⟩)
      (fun h => by rw [φr s h]; exact (hR s ⟨h, hs.2⟩).1)
  · have e : φ =ᶠ[𝓝[Icc 0 S] 0] φL := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
        with y hy using φl y (le_of_lt hy)
    exact (hcφ.continuousWithinAt).congr_of_eventuallyEq e (φl 0 (by norm_num))
  · have hs' : s ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self hs
    exact glue (d := fun y => -(2 / y * φ y) - Real.exp (w y)) hs' hS hφR.symm
      (fun h => by
        simp only [φl s h, wl s h]; exact hdφ s ⟨hs.1, h⟩)
      (fun h => by
        simp only [φr s h, wr s h]; exact (hR s ⟨h, hs.2⟩).2)

end Work.Math.GelfandExists

#print axioms Work.Math.GelfandExists.exists_solution
