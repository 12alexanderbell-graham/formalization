import Checked.FSRev.RBase

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient, the reversed-flow branch: the certified tube shape with a free end time (the tube of `RBase` ends at a fixed time; for larger coefficients the trajectories reach the end region later). Module `RTubeA`, run 2026-11-12T2228Z. -/

namespace Checked.FSRev.RTubeA
open Set Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSRev.RBase

/-- The certified tube shape with end time L: every solution of the clamped coefficient-K field on [0, L] from
(0, 0, α), α ∈ [lo, hi], stays inside the clamps with p > −1/2 and ends in 0 < f < 1, 0 < p < 1,
0 < q < 6/5. -/
def TubeRA (K lo hi L : ℝ) : Prop :=
  ∀ α ∈ Icc lo hi, ∀ Y : ℝ → ℝ × ℝ × ℝ,
    (∀ t ∈ Icc (0 : ℝ) L, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 L) t) →
    Y 0 = (0, 0, α) →
    (∀ t ∈ Icc (0 : ℝ) L, PhiT (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t) ∧
    (0 < (Y L).1 ∧ (Y L).1 < 1 ∧ 0 < (Y L).2.1 ∧ (Y L).2.1 < 1 ∧
      0 < (Y L).2.2 ∧ (Y L).2.2 < 6 / 5)

end Checked.FSRev.RTubeA
