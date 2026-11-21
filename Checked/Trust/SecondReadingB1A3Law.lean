import Checked.Cosmography.Lookback
/-! Blind literal reading of the expansion law of the three-source cubic fit. Copied verbatim (code) from `runs/2026-11-21T1628Z/lit_reader3/SecondReadingB1A3Law.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the claim in words in the brief; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Checked.Cosmography
/-- Three-source cubic fit: the squared Hubble rate over its present value in flat ΛCDM, at time `s`. -/
noncomputable def b1a3Law (Ω : ℝ) (a : ℝ → ℝ) (t₀ s : ℝ) : ℝ := Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω
end Checked.Trust.SecondReading
