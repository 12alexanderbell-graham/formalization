import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Blind literal reading of the regularity condition of the Thomas–Fermi problem (run 2026-11-06T2028Z): continuity of the derivative at the nucleus within the half-line. Copied verbatim (code) from `runs/2026-11-06T2028Z/tf_reader3/SecondReadingTF3.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own knowledge of the model; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Set
/-- Thomas–Fermi problem: φ = y' is continuous at the nucleus within the half-line of scaled distances that starts there. -/
def tfRegular (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Ici 0) 0
end Checked.Trust.SecondReading
