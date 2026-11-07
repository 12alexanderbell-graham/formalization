import Checked.Sim.QResid
import Checked.Sim.RobCell
/-! Validated simulation, `QResidRob`: the defect identities of the generated cells of the stiff chains
`Checked.Sim.RobCerts0` and `Checked.Sim.RobLCerts0` (reduced field `robP`, `robQ`), plain and in a rescaled variable, decided by kernel evaluation (`Checked.Sim.QResid`). -/

namespace Checked.Sim.QResidRob
open Checked.Sim Checked.Sim.QPoly Checked.Sim.QResid Checked.Sim.RobCell

/-- Residual of the equation of the second species (`robP`). -/
def robA (p2 p3 : List ℚ) : List ℚ :=
  qsub (qderiv p2) (qsub (qsub (qsmul (1 / 25) (qsub (qsub [1] p2) p3)) (qsmul 10000 (qmul p2 p3)))
    (qsmul 30000000 (qmul p2 p2)))
/-- Residual of the equation of the third species (`robQ`). -/
def robB (p2 p3 : List ℚ) : List ℚ := qsub (qderiv p3) (qsmul 30000000 (qmul p2 p2))

theorem evalQ_robA (p2 p3 : List ℚ) (u : ℝ) :
    evalQ (robA p2 p3) u = dEvalQ p2 u - robP (evalQ p2 u) (evalQ p3 u) := by
  simp only [robA, evalQ_qsub, evalQ_qsmul, evalQ_qmul, dEvalQ_eq, robP, evalQ]
  push_cast; ring

theorem evalQ_robB (p2 p3 : List ℚ) (u : ℝ) :
    evalQ (robB p2 p3) u = dEvalQ p3 u - robQ (evalQ p2 u) (evalQ p3 u) := by
  simp only [robB, evalQ_qsub, evalQ_qsmul, evalQ_qmul, dEvalQ_eq, robQ]
  push_cast; ring

theorem rob_a (p2 p3 d : List ℚ) (h : allZero (qsub (robA p2 p3) d) = true) (u : ℝ) :
    dEvalQ p2 u - robP (evalQ p2 u) (evalQ p3 u) = evalQ d u := by
  rw [← evalQ_robA, evalQ_eq_of_allZero h u]

theorem rob_b (p2 p3 d : List ℚ) (h : allZero (qsub (robB p2 p3) d) = true) (u : ℝ) :
    dEvalQ p3 u - robQ (evalQ p2 u) (evalQ p3 u) = evalQ d u := by
  rw [← evalQ_robB, evalQ_eq_of_allZero h u]

theorem rob_a_s (p2 p3 d : List ℚ) (r : ℚ) {R : ℝ} (hR : (r : ℝ) = R) (hR0 : R ≠ 0)
    (h : allZero (qsub (qscale r (robA p2 p3)) d) = true) (u : ℝ) :
    dEvalQ p2 u - robP (evalQ p2 u) (evalQ p3 u) = evalQ d (u / R) := by
  rw [← evalQ_robA, ← evalQ_qscale r hR hR0, evalQ_eq_of_allZero h]

theorem rob_b_s (p2 p3 d : List ℚ) (r : ℚ) {R : ℝ} (hR : (r : ℝ) = R) (hR0 : R ≠ 0)
    (h : allZero (qsub (qscale r (robB p2 p3)) d) = true) (u : ℝ) :
    dEvalQ p3 u - robQ (evalQ p2 u) (evalQ p3 u) = evalQ d (u / R) := by
  rw [← evalQ_robB, ← evalQ_qscale r hR hR0, evalQ_eq_of_allZero h]

end Checked.Sim.QResidRob
