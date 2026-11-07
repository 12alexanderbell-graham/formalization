import Checked.Sim.QPoly
/-! Validated simulation, `QResid`: the defect identities of the generated simulator cells decided by
kernel evaluation. A cell certificate supplies a defect polynomial `d` and must show that the residual of
the cell's Taylor polynomials in the field equals `d`; instead of a `ring` proof per cell, the residual is
computed over ℚ (`Checked.Sim.QPoly`) and the difference checked to be the zero list by `decide +kernel`. -/

namespace Checked.Sim.QResid
open Checked.Sim Checked.Sim.QPoly

/-- Every coefficient is zero. -/
def allZero (p : List ℚ) : Bool := p.all (fun c => decide (c = 0))

theorem evalQ_of_allZero {p : List ℚ} (h : allZero p = true) (s : ℝ) : evalQ p s = 0 := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih =>
    simp only [allZero, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [evalQ, h.1, ih h.2]; simp

theorem evalQ_eq_of_allZero {p q : List ℚ} (h : allZero (qsub p q) = true) (s : ℝ) :
    evalQ p s = evalQ q s := by
  have := evalQ_of_allZero h s
  rw [evalQ_qsub] at this; linarith

/-- Rescaling: coefficient k multiplied by rᵏ, so that the result evaluated at u/r is the input at u. -/
def qscale (r : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => a :: qsmul r (qscale r p)

theorem evalQ_qscale (r : ℚ) {R : ℝ} (hR : (r : ℝ) = R) (hR0 : R ≠ 0) (p : List ℚ) (u : ℝ) :
    evalQ (qscale r p) (u / R) = evalQ p u := by
  induction p with
  | nil => simp [qscale, evalQ]
  | cons a p ih =>
    simp only [qscale, evalQ, evalQ_qsmul, ih, hR]
    field_simp

/-! Cells of the oscillator chain `Checked.Sim.DuffingCerts`. -/

/-- Residual of the position equation of the oscillator cells. -/
def dufA (px pv : List ℚ) : List ℚ := qsub (qderiv px) pv
/-- Residual of the velocity equation of the oscillator cells. -/
def dufB (px pv : List ℚ) : List ℚ := qadd (qadd (qderiv pv) px) (qmul px (qmul px px))

theorem duf_a (px pv d : List ℚ) (h : allZero (qsub (dufA px pv) d) = true) (s : ℝ) :
    dEvalQ px s - evalQ pv s = evalQ d s := by
  rw [← evalQ_eq_of_allZero h s, dufA, evalQ_qsub, dEvalQ_eq]

theorem duf_b (px pv d : List ℚ) (h : allZero (qsub (dufB px pv) d) = true) (s : ℝ) :
    dEvalQ pv s + evalQ px s + evalQ px s ^ 3 = evalQ d s := by
  rw [← evalQ_eq_of_allZero h s, dufB, evalQ_qadd, evalQ_qadd, evalQ_qmul, evalQ_qmul, dEvalQ_eq]
  ring

/-! Cells of the enzyme-kinetics chain `Checked.Sim.MMCerts`. -/

/-- Residual of the substrate equation. -/
def mmA (ps pc : List ℚ) : List ℚ :=
  qsub (qderiv ps) (qadd (qadd (qsmul (-1) ps) (qmul pc ps)) pc)
/-- Residual of the complex equation. -/
def mmB (ps pc : List ℚ) : List ℚ :=
  qsub (qderiv pc) (qsub (qsub ps (qmul pc ps)) (qsmul 2 pc))

theorem mm_a (ps pc d : List ℚ) (h : allZero (qsub (mmA ps pc) d) = true) (s : ℝ) :
    dEvalQ ps s - (-evalQ ps s + evalQ pc s * evalQ ps s + evalQ pc s) = evalQ d s := by
  rw [← evalQ_eq_of_allZero h s, mmA, evalQ_qsub, evalQ_qadd, evalQ_qadd, evalQ_qsmul, evalQ_qmul,
    dEvalQ_eq]
  push_cast; ring

theorem mm_b (ps pc d : List ℚ) (h : allZero (qsub (mmB ps pc) d) = true) (s : ℝ) :
    dEvalQ pc s - (evalQ ps s - evalQ pc s * evalQ ps s - 2 * evalQ pc s) = evalQ d s := by
  rw [← evalQ_eq_of_allZero h s, mmB, evalQ_qsub, evalQ_qsub, evalQ_qsub, evalQ_qsmul, evalQ_qmul,
    dEvalQ_eq]
  push_cast; ring

theorem mm_sum (ps pc d : List ℚ) (h : allZero (qsub (qadd ps pc) d) = true) (s : ℝ) :
    evalQ ps s + evalQ pc s = evalQ d s := by
  rw [← evalQ_eq_of_allZero h s, evalQ_qadd]

end Checked.Sim.QResid
