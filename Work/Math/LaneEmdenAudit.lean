import Mathlib
import Checked.Math.LaneEmden
import Checked.Math.LEExists
import Work.Math.LEBlindBridge

/-!
# Audit of the Lane–Emden n = 3 headline (run 2026-11-05T0228Z; annex XL)

1. **Blind restatement closed against the Checked proof.** `blind_closed` is the blind
   restatement of `Work/Math/LaneEmdenBlind.lean` (Sonnet, written from the problem in words: θ
   continuous on [0, 7], one-sided derivative 0 at 0, (ξ²θ')' = −ξ²θ³ on (0, 7), no derivative
   at 7, bounds as closed intervals), proved here from `Checked.Math.LaneEmden.core` through the
   bridge `Work.Math.LEBlindBridge.bridge`. The blind reading assumes less than the program's.
2. **Not vacuous.** `nonvacuous`: a θ, φ exist satisfying every hypothesis of
   `Checked.Math.LaneEmden.laneEmden3_constants` (`Checked.Math.LEExists.exists_solution`:
   Banach fixed point of the Volterra map at the centre, Picard–Lindelöf after), so the
   conclusion holds for an actual solution.
-/

namespace Work.Math.LaneEmdenAudit
open Set

theorem blind_closed (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 7))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Ici 0) 0)
    (hode : ∀ ξ ∈ Set.Ioo (0:ℝ) 7, DifferentiableAt ℝ θ ξ ∧
      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ 3)) ξ) :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0:ℝ) 7 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Set.Ico 0 ξ₁, 0 < θ ξ) ∧
      ξ₁ ∈ Set.Icc (6.896848615 : ℝ) 6.896848625 ∧
      (-(ξ₁ ^ 2 * deriv θ ξ₁)) ∈ Set.Icc (2.018235945 : ℝ) 2.018235955 ∧
      (ξ₁ ^ 3 / (3 * (-(ξ₁ ^ 2 * deriv θ ξ₁)))) ∈ Set.Icc (54.1824805 : ℝ) 54.1824815 := by
  obtain ⟨hθ, hφ0, hφ⟩ := Work.Math.LEBlindBridge.bridge θ hcont hd0 hode
  obtain ⟨ξ₁, ha, hb, hz, hpos, hω1, hω2, hc1, hc2⟩ :=
    Checked.Math.LaneEmden.core θ _ hθ hφ0 hφ h0
  have hne : ξ₁ ≠ 0 := by intro h; rw [h] at ha; norm_num at ha
  simp only [hne, ite_false] at hω1 hω2 hc1 hc2
  exact ⟨ξ₁, ⟨by linarith, by linarith⟩, hz, hpos, ⟨ha, hb⟩, ⟨hω1, hω2⟩, ⟨hc1, hc2⟩⟩

theorem nonvacuous : ∃ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ) ∧
    ContinuousWithinAt φ (Icc 0 7) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ) ∧
    θ 0 = 1 ∧
    ∃ ξ₁ : ℝ, 6.896848615 ≤ ξ₁ ∧ ξ₁ ≤ 6.896848625 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955 ∧
      54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815 := by
  obtain ⟨θ, φ, hθ, hφ0, hφ, h0⟩ := Checked.Math.LEExists.exists_solution
  exact ⟨θ, φ, hθ, hφ0, hφ, h0, Checked.Math.LaneEmden.laneEmden3_constants θ φ hθ hφ0 hφ h0⟩

end Work.Math.LaneEmdenAudit

#print axioms Work.Math.LaneEmdenAudit.blind_closed
#print axioms Work.Math.LaneEmdenAudit.nonvacuous
