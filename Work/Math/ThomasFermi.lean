import Mathlib
import Work.Math.TFReduce
import Work.Math.TFChain

/-!
# Thomas–Fermi equation: initial slope of the neutral-atom solution

The dimensionless Thomas–Fermi equation of the neutral atom: y'' = y^{3/2} / √x for x > 0,
y(0) = 1, y(x) → 0 as x → ∞, with y > 0 on [0, ∞). The initial slope y'(0) of this solution
fixes the Thomas–Fermi energy of neutral atoms. Digits of y'(0) in the literature come from
floating-point computations; this file states a certified enclosure.

Conventions: y and φ are real functions on ℝ (values for x < 0 are never used); φ is the
derivative of y on [0, ∞) (a right derivative at 0) and is continuous at 0 from the right;
y^{3/2} is the real power `y x ^ (3 / 2 : ℝ)` (y x > 0 by hypothesis).

Statement: every such solution has −1.58807103 ≤ y'(0) ≤ −1.58807102.
-/

namespace Work.Math.ThomasFermi
open Set Filter Topology

/-- Every solution y of the Thomas–Fermi equation y'' = y^{3/2}/√x on (0, ∞) with y' = φ on
[0, ∞), φ continuous at 0 from the right, y(0) = 1, y > 0 on [0, ∞) and y(x) → 0 as x → ∞ has
initial slope −1.58807103 ≤ φ(0) ≤ −1.58807102. -/
theorem tf_initial_slope (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (h0 : y 0 = 1) (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hlim : Tendsto y atTop (𝓝 0)) :
    -1.58807103 ≤ φ 0 ∧ φ 0 ≤ -1.58807102 := by
  set W : ℝ → ℝ := fun t => Real.sqrt (y (t ^ 2)) with hWdef
  set P : ℝ → ℝ := fun t => φ (t ^ 2) with hPdef
  have hW : ∀ T : ℝ, ∀ t ∈ Ioc (0 : ℝ) T, HasDerivAt W (t * P t / W t) t :=
    fun T t ht => Work.Math.TFReduce.deriv_W y φ hy hpos t ht.1
  have hP : ∀ T : ℝ, ∀ t ∈ Ioc (0 : ℝ) T, HasDerivAt P (2 * W t ^ 3) t :=
    fun T t ht => Work.Math.TFReduce.deriv_P y φ hφ hpos t ht.1
  have hWp : ∀ T : ℝ, ∀ t ∈ Ioc (0 : ℝ) T, 0 < W t :=
    fun T t _ => Work.Math.TFReduce.W_pos y hpos t
  have hW0 : W 0 = 1 := Work.Math.TFReduce.W_zero y h0
  have hP0 : P 0 = φ 0 := Work.Math.TFReduce.P_zero φ
  constructor
  · by_contra hlt
    push Not at hlt
    have hc := Work.Math.TFCerts.sup_chain (W := W) (P := P)
      (Work.Math.TFReduce.cont_W y φ hy _) (Work.Math.TFReduce.cont_P y φ hφ hφ0 _)
      (hW _) (hP _) (hWp _) hW0 (by rw [hP0]; norm_num at hlt ⊢; linarith)
    exact Work.Math.TFReduce.zero_event y φ hy hφ hφ0 hpos hlim (27 / 4) (13 / 625)
      (771 / 10000000) (by norm_num) (by norm_num) (by norm_num) Work.Math.TFCerts.sup_event
      hc.1.le hc.2.le
  · by_contra hlt
    push Not at hlt
    have hc := Work.Math.TFCerts.sub_chain (W := W) (P := P)
      (Work.Math.TFReduce.cont_W y φ hy _) (Work.Math.TFReduce.cont_P y φ hφ hφ0 _)
      (hW _) (hP _) (hWp _) hW0 (by rw [hP0]; norm_num at hlt ⊢; linarith)
    exact absurd hc (not_lt.2 (Work.Math.TFReduce.phi_neg y φ hy hφ hφ0 hpos hlim _
      (sq_nonneg _)).le)

end Work.Math.ThomasFermi
