# Blind literal reading brief (run 2026-11-12T0427Z): Bonnor–Ebert mass and density contrast

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, `*.md` files, git history). Write only to `runs/2026-11-12T0427Z/be_reader/`. Do not compile. Derive every number yourself from the physics below; nothing external is needed (you may consult textbooks/web for the definitions, but never copy a formula from this repository).

Physics: a self-gravitating isothermal gas sphere (sound speed c_s, gravitational constant G) in hydrostatic equilibrium, truncated at radius R and confined by an external pressure P_ext equal to the gas pressure at R. Density ρ = ρ_c e^{−ψ(ξ)}, dimensionless radius ξ = r / (c_s / √(4πGρ_c)), and ψ is the regular solution of the isothermal Lane–Emden equation. Write w = −ψ and φ = w' (derivative with respect to ξ).

Fill in the capital placeholders with exact numbers (integers or exact fractions) in this Lean template and write it to `runs/2026-11-12T0427Z/be_reader/SecondReadingBE.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
/-! Blind literal reading of the Bonnor–Ebert mass and density contrast (run 2026-11-12T0427Z). -/
namespace Checked.Trust.SecondReading
/-- Bonnor–Ebert sphere: the dimensionless mass m(s) = M G^{3/2} P_ext^{1/2} / c_s⁴ of the sphere truncated at dimensionless radius s, in terms of w = −ψ and φ = w'. -/
noncomputable def beMass (s : ℝ) (w φ : ℝ → ℝ) : ℝ := s ^ A * (-φ s) * Real.exp (w s / B) / Real.sqrt (C * Real.pi)
/-- Bonnor–Ebert sphere: the centre-to-edge density contrast ρ_c / ρ(s) of the sphere truncated at dimensionless radius s, in terms of w = −ψ. -/
noncomputable def beContrast (s : ℝ) (w : ℝ → ℝ) : ℝ := Real.exp (D * w s)
/-- Bonnor–Ebert sphere: the right end of the radial interval on which the claim below states that the mass decreases. -/
def beDecreaseEnd : ℝ := E
end Checked.Trust.SecondReading
```

A, B, C, D: derive from M = 4π ρ_c (c_s²/(4πGρ_c))^{3/2} ξ² ψ'(ξ) and P_ext = ρ_c c_s² e^{−ψ(ξ)} (eliminate ρ_c). Write negative numbers in parentheses, e.g. `(-3)`. E: read it from this sentence of the claim being checked: "the dimensionless mass increases strictly up to a radius between 6.4507514 and 6.4507515 and decreases strictly from there up to the radius 7".

Also write `notes.md`: your derivation in a few lines, and anything you were unsure of. Report both files' contents in your final message.
