# Blind literal reading brief (run 2026-11-15T0228Z): Bonnor–Ebert mass along a sequence of extrema, the half-line domain, the index pattern of the extrema, and the singular-sphere mass

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-15T0228Z/be_all_reader/`. Do not compile Lean. Derive every number yourself from the physics and the description below; you may run your own Python (numpy/scipy/mpmath) in a temporary directory outside the repository to check your derivation numerically. You may consult textbooks or the web for definitions, but never copy anything from this repository. If a web tool fails, is blocked or times out, record the source as "not read"; never fetch the same content with curl, wget or code. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: a self-gravitating isothermal gas sphere (sound speed c_s, gravitational constant G) in hydrostatic equilibrium, truncated at radius R and confined by an external pressure P_ext equal to the gas pressure at R. Density ρ = ρ_c e^{−ψ(ξ)}, dimensionless radius ξ = r / (c_s / √(4πGρ_c)), and ψ is the regular solution of the isothermal Lane–Emden equation (ψ(0) = 0, ψ'(0) = 0). Write w = −ψ and φ = w' (derivative with respect to ξ). The solution is considered on the whole radial half-line, from the centre outwards, with no outer end; the differential equation itself is imposed away from the centre (centre excluded), where it has no singular coefficient.

The claim being checked is about the dimensionless mass m = M G^{3/2} P_ext^{1/2} / c_s⁴ of the truncated sphere as a function of the truncation radius. It numbers all extrema of m as one sequence ξ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (the critical Bonnor–Ebert sphere), and then alternating: maximum, minimum, maximum, minimum, … . It also states the limit of m at large radius: the mass of the singular isothermal sphere (the solution of the same equation that is singular at the centre and has the form ψ = ln(c ξ²) for a constant c; find c yourself).

Fill in the capital placeholders A, B, C, D, E, F, G, H, J, K in this Lean template — keep every other character, including the four import lines, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-15T0228Z/be_all_reader/SecondReadingBEAll.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Set.Basic
/-! Blind literal reading for the every-extremum claim of the Bonnor–Ebert mass (run 2026-11-15T0228Z). -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the closed radial half-line on which the solution is given, from the centre outwards. -/
def beHalfLine : Set ℝ := Ici A
/-- Bonnor–Ebert sphere: the open radial half-line (centre excluded) on which the isothermal equation is imposed. -/
def beOpenHalfLine : Set ℝ := Ioi B
/-- Bonnor–Ebert sphere: the dimensionless mass m = M G^{3/2} P_ext^{1/2} / c_s⁴ of the sphere truncated at the n-th radius ξ n of a sequence of radii, in terms of w = −ψ and φ = w'. -/
noncomputable def beMassSeq (ξ : ℕ → ℝ) (n : ℕ) (w φ : ℝ → ℝ) : ℝ := ξ n ^ C * (-φ (ξ n)) * Real.exp (w (ξ n) / D) / Real.sqrt (E * Real.pi)
/-- Bonnor–Ebert sphere: the radius, in the sequence ξ of extrema of the mass, of the first maximum (the critical sphere). -/
def beFirstMax (ξ : ℕ → ℝ) : ℝ := ξ F
/-- Bonnor–Ebert sphere: the index of the (k+1)-th maximum of the mass in the sequence of extrema. -/
def beMaxIndex (k : ℕ) : ℕ := G
/-- Bonnor–Ebert sphere: the index of the (k+1)-th minimum of the mass in the sequence of extrema. -/
def beMinIndex (k : ℕ) : ℕ := H
/-- Bonnor–Ebert sphere: the index of the (k+2)-th maximum of the mass in the sequence of extrema. -/
def beNextMaxIndex (k : ℕ) : ℕ := J
/-- Bonnor–Ebert sphere: the dimensionless mass of the singular isothermal sphere, the limit of the mass at large radius. -/
noncomputable def beSingularMass : ℝ := Real.sqrt (K / Real.pi)
end Checked.Trust.SecondReading
```

- A, B: the dimensionless radius of the centre (the left end of each half-line).
- C, D, E: derive from M = 4π ρ_c (c_s²/(4πGρ_c))^{3/2} ξ² ψ'(ξ) and P_ext = ρ_c c_s² e^{−ψ(ξ)} at the truncation radius ξ = ξ n (eliminate ρ_c). Exact integers or fractions.
- F: the index, in the sequence described above, of the first maximum.
- G, H, J: for an arbitrary natural number k, the index in the sequence of (G) the (k+1)-th maximum, (H) the (k+1)-th minimum, (J) the (k+2)-th maximum. Write each as `a * k + b` with natural-number literals a and b, and write `a * k` alone (no `+ b`) when b is zero.
- K: an exact rational such that √(K/π) is the dimensionless mass m of the singular isothermal sphere (derive the singular solution, then evaluate m with the C, D, E formula; it is the same at every radius). Check numerically that the regular solution's m approaches this value at large radius and report the first few extrema of m you find.

Write negative numbers in parentheses, e.g. `(-3)`. Also write `notes.md` in the same folder: your derivation in a few lines, the numerical check, and anything you were unsure of. Report both files' contents in your final message.
