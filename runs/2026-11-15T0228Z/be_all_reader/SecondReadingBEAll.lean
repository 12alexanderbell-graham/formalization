import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Set.Basic
/-! Blind literal reading for the every-extremum claim of the Bonnor–Ebert mass (run 2026-11-15T0228Z). -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the closed radial half-line on which the solution is given, from the centre outwards. -/
def beHalfLine : Set ℝ := Ici 0
/-- Bonnor–Ebert sphere: the open radial half-line (centre excluded) on which the isothermal equation is imposed. -/
def beOpenHalfLine : Set ℝ := Ioi 0
/-- Bonnor–Ebert sphere: the dimensionless mass m = M G^{3/2} P_ext^{1/2} / c_s⁴ of the sphere truncated at the n-th radius ξ n of a sequence of radii, in terms of w = −ψ and φ = w'. -/
noncomputable def beMassSeq (ξ : ℕ → ℝ) (n : ℕ) (w φ : ℝ → ℝ) : ℝ := ξ n ^ 2 * (-φ (ξ n)) * Real.exp (w (ξ n) / 2) / Real.sqrt (4 * Real.pi)
/-- Bonnor–Ebert sphere: the radius, in the sequence ξ of extrema of the mass, of the first maximum (the critical sphere). -/
def beFirstMax (ξ : ℕ → ℝ) : ℝ := ξ 0
/-- Bonnor–Ebert sphere: the index of the (k+1)-th maximum of the mass in the sequence of extrema. -/
def beMaxIndex (k : ℕ) : ℕ := 2 * k
/-- Bonnor–Ebert sphere: the index of the (k+1)-th minimum of the mass in the sequence of extrema. -/
def beMinIndex (k : ℕ) : ℕ := 2 * k + 1
/-- Bonnor–Ebert sphere: the index of the (k+2)-th maximum of the mass in the sequence of extrema. -/
def beNextMaxIndex (k : ℕ) : ℕ := 2 * k + 2
/-- Bonnor–Ebert sphere: the dimensionless mass of the singular isothermal sphere, the limit of the mass at large radius. -/
noncomputable def beSingularMass : ℝ := Real.sqrt (2 / Real.pi)
end Checked.Trust.SecondReading
