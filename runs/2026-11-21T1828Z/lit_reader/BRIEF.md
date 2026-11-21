# Blind literal reading brief (run 2026-11-21T1828Z): model and data constants of a cosmology claim

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-21T1828Z/lit_reader/`. Do not compile Lean. You may run your own Python in a temporary directory outside the repository. If you use the web: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read"; never fetch the same content with curl, wget or code.

The claim being checked (cosmology; a cubic log-polynomial fit of the Hubble diagram, as used for quasars by Risaliti & Lusso 2019), in words:

> Take an exactly flat ΛCDM universe (matter and a cosmological constant only, radiation neglected) with present matter density parameter Ω: its expansion rate H at redshift z obeys the Friedmann equation, H(z)² = H₀² times a function of Ω and z. Consider three sources: the nearest at one plus redshift equal to the square root of two, the middle one at one plus redshift equal to twice the square root of two, the farthest at one plus redshift equal to four times the square root of two. Suppose a fitted luminosity-distance curve reproduces that universe's distance modulus (in magnitudes, computed from the luminosity distance in the usual astronomical way) within five hundredths of a magnitude, up to one common offset c, at all three sources.

In the program's Lean, `z a t₀ s` stands for the redshift, seen at time t₀, of light emitted at time s by a universe with scale factor a; a ratio r of two luminosity distances enters the distance-modulus comparison as the modulus difference.

Fill in the capital placeholders in this Lean template — keep every other character, including the import lines, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-21T1828Z/lit_reader/SecondReadingB1A3.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading of the model and data constants of a flat ΛCDM fit-level claim (run 2026-11-21T1828Z). -/
namespace Checked.Trust.SecondReading
/-- Exactly flat ΛCDM with matter density Ω: (H/H₀)² at the redshift z a t₀ s of light emitted at time s and seen at t₀. -/
noncomputable def b1FlatE2 (Ω : ℝ) (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ s : ℝ) : ℝ := Ω * (1 + z a t₀ s) ^ A + B - Ω
/-- The nearest of the three sources: its redshift, emission time t, seen at t₀. -/
noncomputable def b1NearSource (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : Prop := z a t₀ t = √C - D
/-- The middle source: its redshift, emission time t, seen at t₀. -/
noncomputable def b1MiddleSource (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : Prop := z a t₀ t = E * √F - G
/-- The farthest source: its redshift, emission time t, seen at t₀. -/
noncomputable def b1FarSource (z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : Prop := z a t₀ t = J * √K - M
/-- Distance moduli agreeing up to the common offset c within the stated tolerance, for the ratio r of the universe's luminosity distance to the fitted one. -/
noncomputable def b1ModulusWithin (r c : ℝ) : Prop := |N * Real.logb P r - c| ≤ Q / R
end Checked.Trust.SecondReading
```

- A, B, C, D, E, F, G, J, K, M, N, P: natural-number literals (for example `7`, never `7.0`).
- Q / R: the tolerance as a fraction of two natural-number literals in lowest terms.

Also write `notes.md` in the same folder: your reasoning in a few lines (where each number comes from) and anything you were unsure of. Report both files' contents in your final message.
