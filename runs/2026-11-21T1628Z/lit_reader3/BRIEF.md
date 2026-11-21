# Blind literal reading brief (run 2026-11-21T1628Z): the expansion law of a cubic Hubble-diagram comparison

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-21T1628Z/lit_reader3/`. Do not compile Lean.

Cosmology: an exact spatially flat ΛCDM universe of matter density Ω, scale factor `a`, observed at time `t₀`. In it the squared Hubble rate at time `s`, over its present value, is the flat ΛCDM expression in Ω and the redshift of time `s` (matter scaling as the cube of one plus the redshift, and the cosmological constant making up the rest so that the expression is one today). The program writes the redshift of time `s` seen at `t₀` as `redshift a t₀ s` (defined as `a t₀ / a s - 1` in module `Checked.Cosmography.Lookback`, namespace `Checked.Cosmography`).

Fill in the capital placeholders M, N, O in this Lean template with natural-number literals (the smallest that express the quantity in the form given) — keep every other character, including the import line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-21T1628Z/lit_reader3/SecondReadingB1A3Law.lean`:

```lean
import Checked.Cosmography.Lookback
/-! Blind literal reading of the expansion law of the three-source cubic fit (run 2026-11-21T1628Z). -/
namespace Checked.Trust.SecondReading
open Checked.Cosmography
/-- Three-source cubic fit: the squared Hubble rate over its present value in flat ΛCDM, at time `s`. -/
noncomputable def b1a3Law (Ω : ℝ) (a : ℝ → ℝ) (t₀ s : ℝ) : ℝ := Ω * (M + redshift a t₀ s) ^ N + O - Ω
end Checked.Trust.SecondReading
```

Also write `notes.md` in the same folder: your reasoning in a few lines. Report both files' contents in your final message.
