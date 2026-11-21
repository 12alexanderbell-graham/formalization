import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading of the model and data constants of a flat ΛCDM fit-level claim (run 2026-11-21T1828Z). -/
namespace Checked.Trust.SecondReading
/-- Exactly flat ΛCDM with matter density Ω: (H/H₀)² at the redshift z a t₀ s of light emitted at time s and seen at t₀. -/
noncomputable def b1FlatE2 (Ω : ℝ) (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ s : ℝ) : ℝ := Ω * (1 + z a t₀ s) ^ 3 + 1 - Ω
/-- The nearest of the three sources: its redshift, emission time t, seen at t₀. -/
noncomputable def b1NearSource (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : Prop := z a t₀ t = √2 - 1
/-- The middle source: its redshift, emission time t, seen at t₀. -/
noncomputable def b1MiddleSource (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : Prop := z a t₀ t = 2 * √2 - 1
/-- The farthest source: its redshift, emission time t, seen at t₀. -/
noncomputable def b1FarSource (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : Prop := z a t₀ t = 4 * √2 - 1
/-- Distance moduli agreeing up to the common offset c within the stated tolerance, for the ratio r of the universe's luminosity distance to the fitted one. -/
noncomputable def b1ModulusWithin (r c : ℝ) : Prop := |5 * Real.logb 10 r - c| ≤ 1 / 20
end Checked.Trust.SecondReading
