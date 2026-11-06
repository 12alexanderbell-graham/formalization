import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.Basic
/-! Blind literal reading of the Thomas–Fermi problem of the neutral atom (reader: Claude, from own knowledge of the Thomas–Fermi model, no external sources consulted; reading: y'' = y^(3/2) / x^(1/2), y(0) = 1, y(x) → 0 as x → ∞). -/
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
