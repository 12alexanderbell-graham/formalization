# Blind literal reading brief (run 2026-11-12T0628Z): Bonnor–Ebert mass, density contrast and the decrease range

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-12T0628Z/be_reader/`. Do not compile. Derive every number yourself from the physics below; nothing external is needed (you may consult textbooks or the web for the definitions, but never copy a formula from this repository). If a web tool fails, is blocked or times out, record the source as "not read"; never fetch the same content with curl, wget or code.

Physics: a self-gravitating isothermal gas sphere (sound speed c_s, gravitational constant G) in hydrostatic equilibrium, truncated at radius R and confined by an external pressure P_ext equal to the gas pressure at R. Density ρ = ρ_c e^{−ψ(ξ)}, dimensionless radius ξ = r / (c_s / √(4πGρ_c)), and ψ is the regular solution of the isothermal Lane–Emden equation. Write w = −ψ and φ = w' (derivative with respect to ξ).

Fill in the capital placeholders with exact numbers (integers or exact fractions) in this Lean template — keep every other character, including the four import lines, exactly as written — and write it to `runs/2026-11-12T0628Z/be_reader/SecondReadingBE.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Set.Basic
/-! Blind literal reading of the Bonnor–Ebert mass, density contrast and decrease range (run 2026-11-12T0628Z). -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the dimensionless mass m(s) = M G^{3/2} P_ext^{1/2} / c_s⁴ of the sphere truncated at dimensionless radius s, in terms of w = −ψ and φ = w'. -/
noncomputable def beMass (s : ℝ) (w φ : ℝ → ℝ) : ℝ := s ^ A * (-φ s) * Real.exp (w s / B) / Real.sqrt (C * Real.pi)
/-- Bonnor–Ebert sphere: the centre-to-edge density contrast ρ_c / ρ(s) of the sphere truncated at dimensionless radius s, in terms of w = −ψ. -/
noncomputable def beContrast (s : ℝ) (w : ℝ → ℝ) : ℝ := Real.exp (D * w s)
/-- Bonnor–Ebert sphere: the right end of the radial interval on which the claim below states that the mass decreases. -/
def beDecreaseEnd : ℝ := E
/-- Bonnor–Ebert sphere: the closed radial range, from the radius ξ of the maximum to the end stated in the claim, on which the mass decreases. -/
def beDecreaseRange (ξ : ℝ) : Set ℝ := Icc ξ E
end Checked.Trust.SecondReading
```

A, B, C, D: derive from M = 4π ρ_c (c_s²/(4πGρ_c))^{3/2} ξ² ψ'(ξ) and P_ext = ρ_c c_s² e^{−ψ(ξ)} (eliminate ρ_c). Write negative numbers in parentheses, e.g. `(-3)`. E (the same number in both places): read it from this sentence of the claim being checked: "the dimensionless mass increases strictly up to a radius ξ₁ between 6.4507514 and 6.4507515 and decreases strictly from ξ₁ up to the radius 7 (both ends included)".

Also write `notes.md` in the same folder: your derivation in a few lines, and anything you were unsure of. Report both files' contents in your final message.
