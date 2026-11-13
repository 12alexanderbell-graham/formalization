import Checked.FSRev.RBase

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient, the reversed-flow branch with a free clamp level of the shear component: the clamped field, the certified chain shape, the tube side property and the certified tube shape. Module `WBase`, run 2026-11-13T0628Z (the stack of `Checked/FSRev/` clamps the shear at 2; the rows nearest β = 0 of the reversed-flow table need a wider clamp). -/

namespace Checked.FSRevW.WBase
open Set Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSRev.RBase

/-- The clamped coefficient-K field with the adverse pressure sign, shear clamped at level `Cq`. -/
noncomputable def vW (Cq K t : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cl 2 y.2.1, cl Cq y.2.2, -(K * cl (max t 0 + 2) y.1 * cl Cq y.2.2) + 1 - cl 2 y.2.1 ^ 2)

/-- The certified chain shape: every solution of the clamped field on [0, T] from (0, 0, α) has
the event `E`. -/
def ChainW (Cq K α : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vW Cq K t (Y t)) (Icc 0 T) t) →
    Y 0 = (0, 0, α) → E Y

/-- The tube side property: inside the clamps and p > −1/2. -/
def PhiW (Cq : ℝ) (g p q : ℝ → ℝ) (t : ℝ) : Prop :=
  (|g t| ≤ t + 2 ∧ |p t| ≤ 2 ∧ |q t| ≤ Cq) ∧ -1 / 2 < p t

/-- The certified tube shape with end time L: every solution of the clamped field on [0, L] from
(0, 0, α), α ∈ [lo, hi], stays inside the clamps with p > −1/2 and ends in 0 < f < 1, 0 < p < 1,
0 < q < 6/5. -/
def TubeW (Cq K lo hi L : ℝ) : Prop :=
  ∀ α ∈ Icc lo hi, ∀ Y : ℝ → ℝ × ℝ × ℝ,
    (∀ t ∈ Icc (0 : ℝ) L, HasDerivWithinAt Y (vW Cq K t (Y t)) (Icc 0 L) t) →
    Y 0 = (0, 0, α) →
    (∀ t ∈ Icc (0 : ℝ) L, PhiW Cq (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t) ∧
    (0 < (Y L).1 ∧ (Y L).1 < 1 ∧ 0 < (Y L).2.1 ∧ (Y L).2.1 < 1 ∧
      0 < (Y L).2.2 ∧ (Y L).2.2 < 6 / 5)

end Checked.FSRevW.WBase
