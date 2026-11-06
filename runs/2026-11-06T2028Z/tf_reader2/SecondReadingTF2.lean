import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Interval.Set.Defs
/-! Blind literal reading of the regularity condition of the Thomas–Fermi problem (reader: Claude; sources: own knowledge of the Thomas–Fermi model only). -/
namespace Checked.Trust.SecondReading
open Set
/-- Thomas–Fermi problem: φ = y' is continuous at the nucleus within the half-line of scaled distances that starts there. -/
def tfRegular (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Ici 0) 0
end Checked.Trust.SecondReading
