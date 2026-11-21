import Mathlib.Analysis.SpecialFunctions.Log.Base
/-! Blind literal reading of the three-source cubic fit: the redshifts of the three sources, the window on the distance moduli, the distance modulus and the flat ΛCDM expansion law. Copied verbatim (code) from `runs/2026-11-21T1628Z/lit_reader2/SecondReadingB1A3.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the claim in words in the brief; nothing external consulted. -/
namespace Checked.Trust.SecondReading
/-- Three-source cubic fit: the redshift of the nearest source. -/
noncomputable def b1a3zNear : ℝ := √2 - 1
/-- Three-source cubic fit: the redshift of the middle source. -/
noncomputable def b1a3zMid : ℝ := 2 * √2 - 1
/-- Three-source cubic fit: the redshift of the farthest source. -/
noncomputable def b1a3zFar : ℝ := 4 * √2 - 1
/-- Three-source cubic fit: the window on the distance moduli, in magnitudes, as a fraction. -/
noncomputable def b1a3Window : ℝ := 1 / 20
/-- Three-source cubic fit: the distance modulus of a distance ratio `x`, up to the common offset. -/
noncomputable def b1a3Modulus (x : ℝ) : ℝ := 5 * Real.logb 10 x
/-- Three-source cubic fit: the squared Hubble rate over its present value in flat ΛCDM, at redshift `z`. -/
noncomputable def b1a3Radicand (Ω z : ℝ) : ℝ := Ω * (1 + z) ^ 3 + 1 - Ω
end Checked.Trust.SecondReading
