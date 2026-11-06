import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Blind literal reading of the regularity condition of the Thomas–Fermi problem (reader: Claude Sonnet 5.5, subagent tf_reader3; sources: own knowledge of the model and the brief only). -/
namespace Checked.Trust.SecondReading
open Set
/-- Thomas–Fermi problem: φ = y' is continuous at the nucleus within the half-line of scaled distances that starts there. -/
def tfRegular (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Ici 0) 0
end Checked.Trust.SecondReading
