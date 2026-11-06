import Mathlib.Data.Real.Basic
/-! Blind literal reading of the end time of the integration interval and of the printed reference value of the third concentration at that time for the ROBER test problem (run 2026-11-06T1028Z). Copied verbatim (code) from `runs/2026-11-06T1028Z/rob_reader_long/SecondReadingRobLong.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the Bari IVP test set report, problem ROBER, its section on the numerical solution and its table of the reference solution at the end of the integration interval (typeset page seen). The report also says the problem was originally posed on a shorter interval; the test set integrates on the longer one, and the printed reference values belong to it. -/
namespace Checked.Trust.SecondReading
/-- Bari IVP test set, problem ROBER: the end time T of the integration interval [0, T] specified by the test set. -/
noncomputable def robTEnd : ℝ := 10 ^ 11
/-- Bari IVP test set, problem ROBER: the printed reference value of the third component y₃ at the end time T, all printed digits. -/
noncomputable def robY3Ref : ℝ := 9999999791665050 / 10000000000000000
end Checked.Trust.SecondReading
