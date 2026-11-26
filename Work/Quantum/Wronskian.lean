import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-!
# Wronskian sign for two flux-form solutions (run 2026-11-26T1628Z)

Route step 1 of `runs/2026-11-26T1628Z/README.md`: uniqueness of the angular root A(k). For solutions of
(w M′)′ = −Vᵢ M (i = 1, 2) on [0, 1] with the weight vanishing at 0 (the regular singular end s = 0, η = 1),
W = M₁ (w M₂′) − M₂ (w M₁′) has derivative (V₁ − V₂) M₁ M₂ and W(0) = 0. `wronskian_pos`: if
(V₁ − V₂) M₁ M₂ > 0 on (0, 1), then W(1) > 0. For the angular equation V = k(1 − s)² − A, so
V₁ − V₂ = A₂ − A₁ at equal k: with M₁, M₂ > 0 and A₁ < A₂, M₁(1) M₂′(1) > M₂(1) M₁′(1) at s = 1 (η = 0)
(w(1) = 1): if M₁′(1) = 0 then M₂′(1) > 0, so the root of M′(η = 0) in A is unique.
-/

namespace Work.Quantum.Wronskian
open Set

theorem wronskian_pos {w V₁ V₂ M₁ M₂ D₁ D₂ : ℝ → ℝ}
    (hM₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt M₁ (D₁ s) s)
    (hM₂ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt M₂ (D₂ s) s)
    (hF₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun y => w y * D₁ y) (-(V₁ s * M₁ s)) s)
    (hF₂ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun y => w y * D₂ y) (-(V₂ s * M₂ s)) s)
    (hw0 : w 0 = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < (V₁ s - V₂ s) * M₁ s * M₂ s) :
    0 < M₁ 1 * (w 1 * D₂ 1) - M₂ 1 * (w 1 * D₁ 1) := by
  set W : ℝ → ℝ := fun y => M₁ y * (w y * D₂ y) - M₂ y * (w y * D₁ y) with hW
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt W ((V₁ s - V₂ s) * M₁ s * M₂ s) s := by
    intro s hs
    have := ((hM₁ s hs).mul (hF₂ s hs)).sub ((hM₂ s hs).mul (hF₁ s hs))
    convert this using 1
    ring
  have hmono : StrictMonoOn W (Icc (0 : ℝ) 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) ?_ (fun x hx => ?_)
    · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
    · rw [interior_Icc] at hx
      rw [(hder x (Ioo_subset_Icc_self hx)).deriv]
      exact hpos x hx
  have h := hmono (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
  have hW0 : W 0 = 0 := by simp [hW, hw0]
  rw [hW0] at h
  exact h

end Work.Quantum.Wronskian
