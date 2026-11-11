import Checked.FSSep.SBase

/-! Falkner–Skan adverse pressure gradient with a free coefficient K, the reversed-flow branch: the lower
slow-approach event with the K ≥ 5 threshold 11/15, the tube side property and the certified tube shape.
Run 2026-11-11T1228Z (port of `Checked/FSNeg/LCell.lean`'s `SlowL`, `PhiT` and `Checked/FSNeg/LAssemble.lean`'s
`TubeTo` from the K = 10 field `vN` to `Checked.FSSep.SBase.vS K`, 11/30 → 11/15). -/

namespace Work.FSRev.RBase
open Set Checked.FSNeg.NBase Checked.FSSep.SBase

/-- Lower Slow event: at some η > 3/2 the trajectory is in the region 1/3 < p, 0 < q < 3(1 − p),
f > 11/15, having had p < 1 on [0, η]. -/
def SlowR (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η, 3 / 2 < η ∧ (∀ s ∈ Icc 0 η, (Y s).2.1 < 1) ∧ 1 / 3 < (Y η).2.1 ∧ 0 < (Y η).2.2 ∧
    (Y η).2.2 < 3 * (1 - (Y η).2.1) ∧ 11 / 15 < (Y η).1

/-- The tube side property: inside the clamps and p > −1/2. -/
def PhiT (g p q : ℝ → ℝ) (t : ℝ) : Prop := (|g t| ≤ t + 2 ∧ |p t| ≤ 2 ∧ |q t| ≤ 2) ∧ -1 / 2 < p t

/-- The certified tube shape: every solution of the clamped coefficient-K field on [0, 3/2] from
(0, 0, α), α ∈ [lo, hi], stays inside the clamps with p > −1/2 and ends in 0 < f < 1, 0 < p < 1,
0 < q < 6/5. -/
def TubeR (K lo hi : ℝ) : Prop :=
  ∀ α ∈ Icc lo hi, ∀ Y : ℝ → ℝ × ℝ × ℝ,
    (∀ t ∈ Icc (0 : ℝ) (3 / 2), HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 (3 / 2)) t) →
    Y 0 = (0, 0, α) →
    (∀ t ∈ Icc (0 : ℝ) (3 / 2), PhiT (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t) ∧
    (0 < (Y (3 / 2)).1 ∧ (Y (3 / 2)).1 < 1 ∧ 0 < (Y (3 / 2)).2.1 ∧ (Y (3 / 2)).2.1 < 1 ∧
      0 < (Y (3 / 2)).2.2 ∧ (Y (3 / 2)).2.2 < 6 / 5)

end Work.FSRev.RBase
