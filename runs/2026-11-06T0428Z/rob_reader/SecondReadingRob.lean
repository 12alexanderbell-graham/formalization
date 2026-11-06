import Mathlib.Data.Real.Basic
/-! Blind literal reading of Robertson's rate constants (reader: rob_reader, sources: Bari IVP Test Set report "Problem ROBER" (archimede.uniba.it/~testset/report/rober.pdf), typeset secondary description of Robertson 1966; primary paper not seen. Note: that source numbers the constants k1 = 0.04 (A → B), k2 = 3 * 10^7 (2B → B + C), k3 = 10^4 (B + C → A + C); here they are assigned by reaction as in the docstrings. Original interval 0 ≤ t ≤ 40 per that source. -/
namespace Checked.Trust.SecondReading
/-- Robertson (1966): rate constant of the reaction A → B. -/
noncomputable def robK1 : ℝ := 4 / 100
/-- Robertson (1966): rate constant of the reaction B + C → A + C. -/
noncomputable def robK2 : ℝ := 10 ^ 4
/-- Robertson (1966): rate constant of the reaction 2B → B + C. -/
noncomputable def robK3 : ℝ := 3 * 10 ^ 7
/-- Robertson (1966): initial concentrations of A, B, C (in this order), as a triple. -/
noncomputable def robInit : ℝ × ℝ × ℝ := (1, 0, 0)
/-- The end time of the standard integration interval [0, T] of the original problem. -/
noncomputable def robT : ℝ := 40
end Checked.Trust.SecondReading
