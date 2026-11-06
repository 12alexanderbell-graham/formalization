import Mathlib
import Work.Math.GelfandBlind
import Work.Math.Gelfand

/-!
# Gelfand problem in the 3-D ball: the blind restatement, closed

The blind restater's statement `Blind.Gelfand.gelfand_critical` (run 2026-11-06T1228Z: a regular
solution w on [0, ∞), maximum of s² e^{w(s)} over all s > 0 as `IsGreatest` of the image) follows
from the program's frozen headline `Work.Math.Gelfand.gelfand_ball_critical` (solutions on [0, S]
for every S ≥ 41/10): take φ = deriv w, apply the headline on [0, 41/10] for the maximiser, and on
[0, max s (41/10)] for every other s > 0.
-/

namespace Work.Math.GelfandBlindClosed
open Set Filter Topology

/-- The blind regularity predicate gives the hypotheses of the program's headline on every
[0, S]. -/
theorem hyps (w : ℝ → ℝ) (hw : Blind.Gelfand.IsRegularSol w) (S : ℝ) :
    (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (deriv w s) (Icc 0 S) s) ∧
    ContinuousWithinAt (deriv w) (Icc 0 S) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt (deriv w) (-(2 / s * deriv w s) - Real.exp (w s)) (Icc 0 S) s) ∧
    w 0 = 0 := by
  obtain ⟨_, h0, hd0, htend, hode⟩ := hw
  have hz : deriv w 0 = 0 := by
    by_cases hd : DifferentiableAt ℝ w 0
    · exact ((uniqueDiffWithinAt_Ici 0).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hd0)
    · exact deriv_zero_of_not_differentiableAt hd
  have hsub : Icc (0 : ℝ) S ⊆ Ici 0 := Icc_subset_Ici_self
  refine ⟨fun s hs => ?_, ?_, fun s hs => ?_, h0⟩
  · rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hz]; exact hd0.mono hsub
    · exact (hode s h).1.hasDerivAt.hasDerivWithinAt
  · have hc : ContinuousWithinAt (deriv w) (Ioi 0) 0 := by
      rw [ContinuousWithinAt, hz]; exact htend
    exact (continuousWithinAt_Ioi_iff_Ici.1 hc).mono hsub
  · obtain ⟨_, h2, h3⟩ := hode s hs.1
    have e : deriv (deriv w) s = -(2 / s * deriv w s) - Real.exp (w s) := by linarith
    rw [← e]; exact h2.hasDerivAt.hasDerivWithinAt

/-- The blind restatement of the Gelfand critical parameter, proved from the program's headline. -/
theorem blind_closed (w : ℝ → ℝ) (hw : Blind.Gelfand.IsRegularSol w) :
    ∃ s₁ ∈ Icc (4.071496844 : ℝ) 4.071496845,
      IsGreatest ((fun s => s ^ 2 * Real.exp (w s)) '' Ioi 0) (s₁ ^ 2 * Real.exp (w s₁)) ∧
      s₁ ^ 2 * Real.exp (w s₁) ∈ Icc (3.321992118 : ℝ) 3.321992119 := by
  have app : ∀ S : ℝ, 41 / 10 ≤ S → ∃ s₁ : ℝ, 4.071496844 ≤ s₁ ∧ s₁ ≤ 4.071496845 ∧
      (∀ s ∈ Icc 0 S, s ^ 2 * Real.exp (w s) ≤ s₁ ^ 2 * Real.exp (w s₁)) ∧
      3.321992118 ≤ s₁ ^ 2 * Real.exp (w s₁) ∧ s₁ ^ 2 * Real.exp (w s₁) ≤ 3.321992119 := by
    intro S hS
    obtain ⟨a, b, c, d⟩ := hyps w hw S
    exact Work.Math.Gelfand.gelfand_ball_critical S hS w (deriv w) a b c d
  obtain ⟨s₁, h1, h2, hmax, hlo, hhi⟩ := app (41 / 10) le_rfl
  refine ⟨s₁, ⟨h1, h2⟩, ⟨⟨s₁, ?_, rfl⟩, ?_⟩, ⟨hlo, hhi⟩⟩
  · show 0 < s₁; norm_num at h1; linarith
  · rintro y ⟨s, hs, rfl⟩
    obtain ⟨s₂, g1, g2, gmax, -, -⟩ := app (max s (41 / 10)) (le_max_right _ _)
    have hs' : s ∈ Icc 0 (max s (41 / 10)) := ⟨le_of_lt hs, le_max_left _ _⟩
    have h22 : s₂ ∈ Icc (0 : ℝ) (41 / 10) := ⟨by norm_num at g1; linarith, by norm_num at g2; linarith⟩
    exact (gmax s hs').trans (hmax s₂ h22)

end Work.Math.GelfandBlindClosed

#print axioms Work.Math.GelfandBlindClosed.blind_closed
