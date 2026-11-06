import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.Basic
/-! Blind literal reading of the Thomas–Fermi problem of the neutral atom (run 2026-11-06T2028Z): the right-hand side of the equation, the half-line of scaled distances, the condition at the nucleus, the limit at infinity and evaluation at the nucleus. Copied verbatim (code) from `runs/2026-11-06T2028Z/tf_reader/SecondReadingTF.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own knowledge of the Thomas–Fermi model; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Thomas–Fermi equation of the neutral atom: the right-hand side of y'' at a scaled distance x > 0. -/
noncomputable def tfRhs (y : ℝ → ℝ) (x : ℝ) : ℝ := y x ^ ((3 : ℝ) / 2) / Real.sqrt x
/-- Thomas–Fermi problem: the closed half-line of scaled distances, starting at the nucleus. -/
def tfDomain : Set ℝ := Ici 0
/-- Thomas–Fermi problem: the boundary condition at the nucleus (its scaled distance, then the value of y there). -/
def tfNucleus (y : ℝ → ℝ) : Prop := y 0 = 1
/-- Thomas–Fermi problem of the neutral atom: the limit of y at infinity, as a neighbourhood filter of that value. -/
noncomputable def tfInfinity : Filter ℝ := 𝓝 0
/-- Thomas–Fermi problem: a function evaluated at the nucleus (used for the initial slope y'(nucleus)). -/
def tfAtNucleus (φ : ℝ → ℝ) : ℝ := φ 0
end Checked.Trust.SecondReading
