import Mathlib.Data.Real.Basic
/-! Blind literal reading of the ROBER test problem's integration end time and printed reference value (reader: independent blind reader, sources: Bari IVP Test Set report, ODE - Problem ROBER, Section 10.4 "Numerical solution of the problem" (integrated for t in [0, 10^11], page II-10-2/3) and Table II.10.3 "Reference solution at the end of the integration interval" (page II-10-3), typeset page seen. The report text also says the problem was originally posed on 0 <= t <= 40, but the test set integrates on [0, 10^11]; the Table II.10.3 values are for the end of that interval. -/
namespace Checked.Trust.SecondReading
/-- Bari IVP test set, problem ROBER: the end time T of the integration interval [0, T] specified by the test set. -/
noncomputable def robTEnd : ℝ := 10 ^ 11
/-- Bari IVP test set, problem ROBER: the printed reference value of the third component y₃ at the end time T, all printed digits. -/
noncomputable def robY3Ref : ℝ := 9999999791665050 / 10000000000000000
end Checked.Trust.SecondReading
