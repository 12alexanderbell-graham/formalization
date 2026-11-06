import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Checked.Math.TFReduce
import Checked.Math.TFChain

/-! Thomas–Fermi, `ThomasFermi`: the initial slope of the neutral-atom Thomas–Fermi function; bounds as printed in the statement of `tf_initial_slope`. Promoted from `Work/Math/ThomasFermi.lean`. -/

namespace Checked.Math.ThomasFermi
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
    fun T t ht => Checked.Math.TFReduce.deriv_W y φ hy hpos t ht.1
  have hP : ∀ T : ℝ, ∀ t ∈ Ioc (0 : ℝ) T, HasDerivAt P (2 * W t ^ 3) t :=
    fun T t ht => Checked.Math.TFReduce.deriv_P y φ hφ hpos t ht.1
  have hWp : ∀ T : ℝ, ∀ t ∈ Ioc (0 : ℝ) T, 0 < W t :=
    fun T t _ => Checked.Math.TFReduce.W_pos y hpos t
  have hW0 : W 0 = 1 := Checked.Math.TFReduce.W_zero y h0
  have hP0 : P 0 = φ 0 := Checked.Math.TFReduce.P_zero φ
  constructor
  · by_contra hlt
    push Not at hlt
    have hc := Checked.Math.TFCerts.sup_chain (W := W) (P := P)
      (Checked.Math.TFReduce.cont_W y φ hy _) (Checked.Math.TFReduce.cont_P y φ hφ hφ0 _)
      (hW _) (hP _) (hWp _) hW0 (by rw [hP0]; norm_num at hlt ⊢; linarith)
    exact Checked.Math.TFReduce.zero_event y φ hy hφ hφ0 hpos hlim (27 / 4) (13 / 625)
      (771 / 10000000) (by norm_num) (by norm_num) (by norm_num) Checked.Math.TFCerts.sup_event
      hc.1.le hc.2.le
  · by_contra hlt
    push Not at hlt
    have hc := Checked.Math.TFCerts.sub_chain (W := W) (P := P)
      (Checked.Math.TFReduce.cont_W y φ hy _) (Checked.Math.TFReduce.cont_P y φ hφ hφ0 _)
      (hW _) (hP _) (hWp _) hW0 (by rw [hP0]; norm_num at hlt ⊢; linarith)
    exact absurd hc (not_lt.2 (Checked.Math.TFReduce.phi_neg y φ hy hφ hφ0 hpos hlim _
      (sq_nonneg _)).le)

end Checked.Math.ThomasFermi
