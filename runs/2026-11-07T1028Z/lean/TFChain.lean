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
import Checked.Sim.ODETools
import Checked.Math.LECell
import Checked.Math.TFCell
import Checked.Math.TFCellQ
import Checked.Math.TFQData

/-! Thomas–Fermi, `TFChain`: chaining the generated barrier cells over the whole interval for both shooting directions. Promoted from `Work/Math/TFChain.lean`. -/

namespace Checked.Math.TFCerts
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.TFCellQ

theorem sup_chain {W P : ℝ → ℝ} (hcW : ContinuousOn W (Icc 0 (27/4 : ℝ))) (hcP : ContinuousOn P (Icc 0 (27/4 : ℝ)))
    (hW : ∀ t ∈ Ioc (0:ℝ) (27/4 : ℝ), HasDerivAt W (t * P t / W t) t)
    (hP : ∀ t ∈ Ioc (0:ℝ) (27/4 : ℝ), HasDerivAt P (2 * W t ^ 3) t)
    (hpos : ∀ t ∈ Ioc (0:ℝ) (27/4 : ℝ), 0 < W t)
    (h0 : W 0 = 1) (hp0 : P 0 < -158807103/100000000) : W (27/4 : ℝ) < (13/625 : ℝ) ∧ P (27/4 : ℝ) < -(771/10000000 : ℝ) := by
  have hs : TFSol ((27/4 : ℚ) : ℝ) W P := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> assumption
  have c0 : W ((TFQData.u0.t0 : ℚ) : ℝ) < ((TFQData.u0.qw.headD 0 : ℚ) : ℝ) ∧
      P ((TFQData.u0.t0 : ℚ) : ℝ) < ((TFQData.u0.qp.headD 0 : ℚ) : ℝ) := by
    simp only [TFQData.u0, List.headD_cons]; push_cast; rw [h0]; constructor <;> linarith
  have c1 := sup_seg_q hs _ _ _ TFQData.useg0_ok c0.1 c0.2
  have c2 := sup_seg_q hs _ _ _ TFQData.useg1_ok c1.1 c1.2
  have c3 := sup_seg_q hs _ _ _ TFQData.useg2_ok c2.1 c2.2
  have c4 := sup_seg_q hs _ _ _ TFQData.useg3_ok c3.1 c3.2
  have c5 := sup_seg_q hs _ _ _ TFQData.useg4_ok c4.1 c4.2
  have he := sup_end_q hs _ _ TFQData.useg5_ok c5.1 c5.2
  push_cast at he
  exact ⟨lt_of_lt_of_le he.1 (by norm_num), lt_of_lt_of_le he.2 (by norm_num)⟩

theorem sup_event : 4 * (13/625 : ℝ) ^ 5 < (27/4 : ℝ) * (771/10000000 : ℝ) ^ 2 := by norm_num

theorem sub_chain {W P : ℝ → ℝ} (hcW : ContinuousOn W (Icc 0 (15/2 : ℝ))) (hcP : ContinuousOn P (Icc 0 (15/2 : ℝ)))
    (hW : ∀ t ∈ Ioc (0:ℝ) (15/2 : ℝ), HasDerivAt W (t * P t / W t) t)
    (hP : ∀ t ∈ Ioc (0:ℝ) (15/2 : ℝ), HasDerivAt P (2 * W t ^ 3) t)
    (hpos : ∀ t ∈ Ioc (0:ℝ) (15/2 : ℝ), 0 < W t)
    (h0 : W 0 = 1) (hp0 : -158807102/100000000 < P 0) : 0 < P (15/2 : ℝ) := by
  have hs : TFSol ((15/2 : ℚ) : ℝ) W P := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> assumption
  have c0 : ((TFQData.l0.qw.headD 0 : ℚ) : ℝ) < W ((TFQData.l0.t0 : ℚ) : ℝ) ∧
      ((TFQData.l0.qp.headD 0 : ℚ) : ℝ) < P ((TFQData.l0.t0 : ℚ) : ℝ) := by
    simp only [TFQData.l0, List.headD_cons]; push_cast; rw [h0]; constructor <;> linarith
  have c1 := sub_seg_q hs _ _ _ TFQData.lseg0_ok c0.1 c0.2
  have c2 := sub_seg_q hs _ _ _ TFQData.lseg1_ok c1.1 c1.2
  have c3 := sub_seg_q hs _ _ _ TFQData.lseg2_ok c2.1 c2.2
  have c4 := sub_seg_q hs _ _ _ TFQData.lseg3_ok c3.1 c3.2
  have c5 := sub_seg_q hs _ _ _ TFQData.lseg4_ok c4.1 c4.2
  have he := sub_end_q hs _ _ TFQData.lseg5_ok c5.1 c5.2
  push_cast at he
  exact lt_of_le_of_lt (by norm_num) he.2

end Checked.Math.TFCerts
