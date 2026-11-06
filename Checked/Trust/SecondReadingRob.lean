import Mathlib.Data.Real.Basic
/-! Blind literal reading of the rate constants, initial concentrations and end time of Robertson's stiff reaction network (run 2026-11-06T0428Z). Copied verbatim (code) from `runs/2026-11-06T0428Z/rob_reader/SecondReadingRob.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the Bari IVP test set report, problem ROBER (a secondary description; the primary paper was not seen). That source numbers the second and third rate constants the other way round; the reader assigned them by reaction, as the docstrings say. -/
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
